import LeanApi

namespace Tests.Http

open LeanApi LeanApi.Test Lean

structure Title where
  raw : String
  deriving Repr, BEq

instance : SmartCtor Title String where
  make s := let t := s.trimAscii.toString; if t.isEmpty then .error "title must be nonempty" else .ok ⟨t⟩
  raw := (·.raw)

structure NewNote where
  title : Title
  body : String
  pinned : Bool

def decodeNote : Extract NewNote := fun r => do
  let j ← Extract.rawJson r
  let (t, b, p) ← (both (field "body" j "title") (both (field "body" j "body") (fieldD "body" j "pinned" false))).map fun (a, b, c) => (a, b, c)
  return { title := t, body := b, pinned := p }

def routes : List Route := routes! [
  Route.get "/" fun _ => pure (Res.text "ok"),
  Route.get "/games/new" fun _ => pure (Res.text "new"),
  Route.get "/games/{id:int}" fun r => pure (Res.text s!"int {r.param? "id" |>.getD ""}"),
  Route.get "/games/{slug}" fun r => pure (Res.text s!"slug {r.param? "slug" |>.getD ""}"),
  Route.post "/games" (handleJson decodeNote fun n => pure (Res.created (Json.mkObj [("title", .str n.title.raw), ("pinned", .bool n.pinned)]) "/games/1")),
  Route.get "/files/{*path}" fun r => pure (Res.text s!"file {r.param? "path" |>.getD ""}"),
  Route.get "/search" (handle ((·, ·) <$> Extract.query (α := Nat) "page" <*> Extract.queryD "q" "") fun (p, q) =>
    pure (Res.text s!"page {p} q {q}")),
  (Route.post "/small" fun r => pure (Res.text s!"got {r.body.size}")).limit 10,
  Route.post "/form" (handle ((·, ·) <$> Extract.form (α := Title) "title" <*> Extract.formOpt (α := Nat) "n") fun (t, n) =>
    pure (Res.text s!"{t.raw} {n}")),
  Route.get "/boom" fun _ => throw (IO.userError "secret internal detail"),
  Route.get "/cookie" fun r => pure ((Res.text s!"sid={r.cookie? "sid" |>.getD "-"}").setCookie { name := "seen", value := "1" }),
  Route.get "/json-only" (requireAccept ["application/json"] fun _ => pure (Res.json (Json.mkObj []))),
  Route.delete "/games/{id:int}" fun _ => pure (Res.empty 204)
]

def svc : Service := Service.ofRouter (Router.build! routes) (Stack.of [recover (fun _ => pure ())])

def run : TestM Unit := do
  section_ "M0: empty route through the test transport" do
    let r ← get svc "/"
    checkEq "GET / status" r.status 200
    checkEq "GET / body" r.body "ok"

  section_ "routing precedence and params" do
    checkEq "literal beats param" (← get svc "/games/new").body "new"
    checkEq "int beats plain" (← get svc "/games/42").body "int 42"
    checkEq "plain param" (← get svc "/games/abc").body "slug abc"
    checkEq "percent-decoded param" (← get svc "/games/a%20b").body "slug a b"
    checkEq "encoded slash stays in segment" (← get svc "/games/a%2Fb").body "slug a/b"
    checkEq "catch-all" (← get svc "/files/a/b/c.txt").body "file a/b/c.txt"
    checkEq "catch-all empty" (← get svc "/files").body "file "
    checkEq "404" (← get svc "/nope").status 404
    checkEq "404 problem+json" ((← get svc "/nope").header? "content-type") (some "application/problem+json")
    checkEq "dot segments refused" (← get svc "/games/../x").status 400

  section_ "405, HEAD, OPTIONS, trailing slash" do
    let r ← request svc "PUT" "/games/1" [] "x"
    checkEq "405" r.status 405
    checkEq "Allow" (r.header? "allow") (some "GET, HEAD, DELETE, OPTIONS")
    let h ← request svc "HEAD" "/games/new"
    checkEq "HEAD status" h.status 200
    checkEq "HEAD no body" h.body ""
    checkEq "HEAD keeps content-length" (h.header? "content-length") (some "3")
    let o ← request svc "OPTIONS" "/games/1"
    checkEq "OPTIONS 204" o.status 204
    checkEq "OPTIONS Allow" (o.header? "allow") (some "GET, HEAD, DELETE, OPTIONS")
    let t ← get svc "/games/new/?x=1"
    checkEq "trailing slash redirect" t.status 308
    checkEq "redirect location" (t.header? "location") (some "/games/new?x=1")
    checkEq "trailing slash on POST is 404" (← request svc "POST" "/games/" [] "").status 404
    let strict := Service.ofRouter (Router.build! routes .strict)
    checkEq "strict trailing slash" (← get strict "/games/new/").status 404
    let ign := Service.ofRouter (Router.build! routes .ignore)
    checkEq "ignore trailing slash" (← get ign "/games/new/").body "new"

  section_ "route table validation" do
    let bad := Router.build [Route.get "/a/{x}" (fun _ => pure {}), Route.get "/a/{y}" (fun _ => pure {})]
    check "duplicate shape rejected" (match bad with | .error _ => true | .ok _ => false)
    let ok := Router.build [Route.get "/a/{x}" (fun _ => pure {}), Route.post "/a/{y}" (fun _ => pure {})]
    check "different methods allowed" (match ok with | .ok _ => true | .error _ => false)
    check "catch-all must be last" ((parseTemplate "/a/{*r}/b").toOption.isNone)
    check "duplicate names rejected" ((parseTemplate "/a/{x}/{x}").toOption.isNone)
    check "group prefixes" ((group "/api" [Route.get "/x" (fun _ => pure {})]).map (·.template) == ["/api/x"])

  section_ "extraction and validation" do
    let r ← postJson svc "/games" (Json.mkObj [("title", .str "  hi "), ("body", .str "b")])
    checkEq "valid json 201" r.status 201
    checkEq "location" (r.header? "location") (some "/games/1")
    checkEq "smart ctor trims" ((r.json?.bind fun j => (j.getObjValAs? String "title").toOption)) (some "hi")
    let r ← postJson svc "/games" (Json.mkObj [("title", .str " "), ("pinned", .str "x")])
    checkEq "invalid fields 422" r.status 422
    let locs := (r.json?.bind fun j => (j.getObjVal? "errors").toOption).bind fun e =>
      match e with
      | .arr xs => some (xs.toList.filterMap fun x => (x.getObjValAs? String "loc").toOption)
      | _ => none
    checkEq "all field locations reported" locs (some ["body.title", "body.body", "body.pinned"])
    let r ← request svc "POST" "/games" [("Content-Type", "application/json")] "{nope"
    checkEq "malformed json 400" r.status 400
    let r ← request svc "POST" "/games" [("Content-Type", "text/plain")] "{}"
    checkEq "wrong content type 415" r.status 415
    checkEq "query ok" (← get svc "/search?page=2&q=a+b").body "page 2 q a b"
    let r ← get svc "/search?page=x"
    checkEq "query invalid 422" r.status 422
    check "query location" (r.body.contains "query.page")
    checkEq "query missing 422" (← get svc "/search").status 422
    let r ← request svc "POST" "/form" [("Content-Type", "application/x-www-form-urlencoded")] "title=Hello+there&n=3"
    checkEq "form" r.body "Hello there (some 3)"
    let r ← request svc "POST" "/form" [("Content-Type", "application/x-www-form-urlencoded")] "title=+"
    check "form smart ctor error" (r.status == 422 && r.body.contains "body.title")

  section_ "limits, errors, cookies, negotiation" do
    checkEq "under limit" (← request svc "POST" "/small" [] "123456789").body "got 9"
    checkEq "over limit 413" (← request svc "POST" "/small" [] "12345678901").status 413
    let chunked := "POST /small HTTP/1.1\r\nHost: t\r\nConnection: close\r\nTransfer-Encoding: chunked\r\n\r\n6\r\n123456\r\n6\r\n123456\r\n0\r\n\r\n"
    checkEq "chunked over limit 413" (parseReply (← sendRaw svc chunked.toUTF8)).status 413
    let r ← get svc "/boom"
    checkEq "exception 500" r.status 500
    check "no internal detail leaked" (!r.body.contains "secret")
    let r ← get svc "/cookie" [("Cookie", "a=1; sid=xyz")]
    checkEq "cookie read" r.body "sid=xyz"
    checkEq "set-cookie" (r.header? "set-cookie") (some "seen=1; Path=/; HttpOnly; Secure; SameSite=Lax")
    checkEq "406" (← get svc "/json-only" [("Accept", "text/html")]).status 406
    checkEq "accept wildcard" (← get svc "/json-only" [("Accept", "text/html, */*;q=0.1")]).status 200
    checkEq "unsupported method 501" (← request svc "PROPFIND" "/" []).status 501

end Tests.Http
