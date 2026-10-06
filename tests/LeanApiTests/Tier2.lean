import LeanApi
import PrivateGames.App.Service

namespace Tests.Tier2

open LeanApi LeanApi.Test Lean

def run : TestM Unit := do
  section_ "conditional requests" do
    let routes := [Route.get "/doc" fun _ => pure ((Res.text "v1").setHeader "etag" "\"7\"" |>.setHeader "last-modified" "Tue, 22 Sep 2026 10:00:00 GMT")]
    let svc := Service.ofRouter (Router.build! routes) (Stack.of [conditionalGet, ifModifiedSince])
    let r ← get svc "/doc" [("If-None-Match", "\"7\"")]
    checkEq "If-None-Match hit → 304" r.status 304
    checkEq "304 keeps etag" (r.header? "etag") (some "\"7\"")
    checkEq "304 has no body" r.body ""
    checkEq "weak match" (← get svc "/doc" [("If-None-Match", "W/\"7\"")]).status 304
    checkEq "list match" (← get svc "/doc" [("If-None-Match", "\"1\", \"7\"")]).status 304
    checkEq "miss → 200" (← get svc "/doc" [("If-None-Match", "\"8\"")]).status 200
    checkEq "If-Modified-Since equal → 304" (← get svc "/doc" [("If-Modified-Since", "Tue, 22 Sep 2026 10:00:00 GMT")]).status 304
    let req := Req.mk' .put "/doc" [("if-match", "\"6\"")]
    checkEq "If-Match mismatch → 412" ((checkIfMatch req (some "\"7\"")).map (·.status)) (some 412)
    checkEq "If-Match match → proceed" ((checkIfMatch (Req.mk' .put "/doc" [("if-match", "\"7\"")]) (some "\"7\"")).map (·.status)) none
    checkEq "If-Match required → 428" ((checkIfMatch (Req.mk' .put "/doc") (some "\"7\"") true).map (·.status)) (some 428)
    let writes ← IO.mkRef (0 : Nat)
    let writeRoutes := [
      Route.put "/unsafe" fun _ => do
        writes.modify (· + 1)
        pure ((Res.text "written").setHeader "etag" "\"7\""),
      Route.put "/checked" fun req => do
        if let some refusal := checkIfNoneMatch req (some "\"7\"") then
          pure refusal
        else
          writes.modify (· + 1)
          pure (Res.text "written")]
    let writeSvc := Service.ofRouter (Router.build! writeRoutes) (Stack.of [conditionalGet])
    checkEq "post-handler middleware never reports false 412"
      (← request writeSvc "PUT" "/unsafe" [("If-None-Match", "\"7\"")]).status 200
    checkEq "unsafe handler ran" (← writes.get) 1
    checkEq "pre-write check refuses matching tag"
      (← request writeSvc "PUT" "/checked" [("If-None-Match", "\"7\"")]).status 412
    checkEq "pre-write refusal leaves state alone" (← writes.get) 1

  section_ "rate limiting" do
    let rl ← RateLimit.new 1.0 3
    let clock ← IO.mkRef 1000
    let svc := Service.ofRouter (Router.build! [Route.get "/" fun _ => pure (Res.text "ok")])
      (Stack.of [rateLimit rl (fun _ => "k") clock.get])
    let mut codes := #[]
    for _ in [0:5] do codes := codes.push (← get svc "/").status
    checkEq "burst then 429" codes #[200, 200, 200, 429, 429]
    let r ← get svc "/"
    checkEq "retry-after" (r.header? "retry-after") (some "1")
    clock.set 2100
    checkEq "refills" (← get svc "/").status 200

  section_ "SSE, tracing, multipart" do
    let e : SseEvent := { data := "a\nb", event := some "move", id := some "3" }
    checkEq "sse format" e.render "event: move\nid: 3\ndata: a\ndata: b\n\n"
    checkEq "sse content type" ((sseRes [e]).header? "content-type") (some "text/event-stream")
    let svc := Service.ofRouter (Router.build! [Route.get "/t" fun r => pure (Res.text ((r.local? "trace-id").getD "-"))]) (Stack.of [tracing])
    let tp := "00-4bf92f3577b34da6a3ce929d0e0e4736-00f067aa0ba902b7-01"
    let r ← get svc "/t" [("traceparent", tp)]
    checkEq "trace continued" r.body "4bf92f3577b34da6a3ce929d0e0e4736"
    check "new span id" ((r.header? "traceparent").any fun v => v.startsWith "00-4bf92f3577b34da6a3ce929d0e0e4736-" && !v.contains "00f067aa0ba902b7")
    let r ← get svc "/t" [("traceparent", "garbage")]
    checkEq "invalid traceparent: new trace" r.body.length 32
    let body := "--XyZ\r\nContent-Disposition: form-data; name=\"title\"\r\n\r\nhello\r\n--XyZ\r\nContent-Disposition: form-data; name=\"file\"; filename=\"a.txt\"\r\nContent-Type: text/plain\r\n\r\nline1\r\nline2\r\n--XyZ--\r\n"
    let mp := Service.ofRouter (Router.build! [Route.post "/up" (handle Extract.multipart fun ps =>
      pure (Res.text (", ".intercalate (ps.map fun p => s!"{p.name}:{p.filename.getD "-"}:{String.fromUTF8! p.data}")))) ])
    let r ← request mp "POST" "/up" [("Content-Type", "multipart/form-data; boundary=XyZ")] body
    checkEq "multipart parts" r.body "title:-:hello, file:a.txt:line1\r\nline2"
    checkEq "multipart malformed 422" (← request mp "POST" "/up" [("Content-Type", "multipart/form-data; boundary=XyZ")] "--XyZ\r\nnope").status 422

  section_ "typed middleware stages" do
    let stages := [Stage.requireJsonBodies, Stage.securityHeaders]
    let svc := Service.ofRouter (Router.build! [Route.post "/x" fun _ => pure (Res.text "ok")]) (Stack.ofStages stages)
    checkEq "guard refuses" (← request svc "POST" "/x" [("Content-Type", "text/plain")] "hi").status 415
    let r ← request svc "POST" "/x" [("Content-Type", "application/json")] "{}"
    checkEq "guard passes" r.body "ok"
    checkEq "decorate adds header" (r.header? "x-frame-options") (some "DENY")
    check "stages describe observations" ((describeStages stages).contains "observes")

  section_ "OpenAPI and coverage (private-games)" do
    let docs : Docs := PrivateGames.App.routeTable.map fun (op, m, t) =>
      ((m, t), { summary := op.name, proved := true, security := true,
                 responses := [(200, "OK"), (401, "Unauthorized"), (404, "Not found or not visible")] })
    let rt ← PrivateGames.Storage.Runtime.open ".lake/test-db/openapi.sqlite" 1
    let r := Router.build! (PrivateGames.App.routes rt.repo "x")
    let spec := r.openApi docs "private-games" "0.4.0"
    check "openapi version" ((spec.getObjValAs? String "openapi").toOption == some "3.1.0")
    let paths := (spec.getObjVal? "paths").toOption
    check "path template rendered" ((paths.bind fun p => (p.getObjVal? "/games/{id}").toOption).isSome)
    check "integer path param" (spec.compress.contains "\"minimum\":0")
    check "proved marker" (spec.compress.contains "\"x-leanapi-proved\":true")
    let cov := r.coverage docs
    checkEq "5 proved routes" cov.proved.length 5
    checkEq "unproved routes are the declared account routes" (cov.undeclared ["POST /players", "POST /sessions"]) []
    IO.println (cov.report.splitOn "\n" |>.map ("    " ++ ·) |> "\n".intercalate)
    let dsvc := Service.ofRouter (Router.build! (docsRoutes spec "private-games"))
    checkEq "/openapi.json served" (← get dsvc "/openapi.json").status 200
    check "/docs page" ((← get dsvc "/docs").body.contains "openapi.json")
    rt.close

end Tests.Tier2
