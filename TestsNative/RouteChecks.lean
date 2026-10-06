import LeanDb.Model
import LeanApi.Core
import LeanApi.Native
import LeanApi.Runtime.TestClient

/-! Routes and sessions over the actual HTTP framing and SQLite: an `Api` with templates and a
GET, cookie and bearer sessions, token mode (decision 9), rotation, expiry, CSRF, path binding
and a page negotiated with a GET endpoint. `leanapi_native_checks routes` runs the checks in
process; `leanapi_native_checks routes --serve` serves the same app on a socket for
`scripts/ddd_route_acceptance.mjs` (real curl/fetch). -/
namespace RouteChecks
open LeanDb.Model LeanApi.Core

structure Person where
  name : Name
  email : Email
  deriving Entity

structure Login where
  person : Ref Person
  hash : PasswordHash
  deriving Entity

structure Party where
  host : Ref Person
  title : Title
  date : Time
  deriving Entity

structure Guest where
  party : Ref Party
  person : Ref Person
  deriving Entity

credential Login.person Login.hash
constraint Person.uniqueEmail : unique email
constraint Guest.once : unique (party, person)

structure SignedIn where
  private mk ::
  id : Ref Person
  deriving Principal

inductive SignUpError where
  | emailTaken

inductive SignInError where
  | invalidCredentials

inductive PartyError where
  | partyMissing

inductive CancelError where
  | partyMissing
  | hostOnly

def signUp (name : Name) (email : Email) (password : Password) : Op SignUpError Session := do
  match ← Person.insert { name, email } with
  | .error .uniqueEmail => throw .emailTaken
  | .ok id =>
    let _ ← Login.insert { person := id, hash := ← password.hash }
    Auth.startSession id

def signIn (email : Email) (password : Password) : Op SignInError Session := do
  let some id ← Login.verify (← Person.findBy email) password | throw .invalidCredentials
  Auth.startSession id

def host (me : SignedIn) (title : Title) (date : Time) : Op Empty (Ref Party) :=
  Party.insert { host := me.id, title, date }

def rsvp (me : SignedIn) (party : Ref Party) : Op PartyError Unit := do
  let some p ← Party.find party | throw .partyMissing
  match ← Guest.insert { party := p.id, person := me.id } with
  | .ok _ => pure ()
  | .error .once => pure ()

def partyTitle (viewer : Option SignedIn) (party : Ref Party) : ReadOp PartyError Title := do
  let some p ← Party.find party | throw .partyMissing
  return p.title

-- Exists and is valid, but is not in the api: never routable.
def cancel (me : SignedIn) (party : Ref Party) : Op CancelError Unit := do
  let some p ← Party.find party | throw .partyMissing
  let ⟨_⟩ ← require (me.id == p.host) .hostOnly
  Party.delete p
derive_operation cancel

def api : Api := [
  post "/sign-up"             signUp,
  post "/sign-in"             signIn,
  post "/parties"             host,
  get  "/parties/:party"      partyTitle,
  post "/parties/:party/rsvp" rsvp
]

end RouteChecks

-- At top level, as in an app's Main: the app% name is fully qualified.
app% RouteChecks.app where
  authentication := RouteChecks.Person with RouteChecks.Login
  api := RouteChecks.api

namespace RouteChecks
open LeanDb.Model LeanApi.Core

/-! ## Checks -/

structure Results where
  passed : Nat := 0
  failed : List String := []

abbrev CheckM := StateT Results IO

def expect (condition : Bool) (label : String) : CheckM Unit :=
  modify fun r => if condition then { r with passed := r.passed + 1 } else { r with failed := r.failed ++ [label] }

def jsonOf (reply : LeanApi.Test.Reply) : Lean.Json := (Lean.Json.parse reply.body).toOption.getD .null

def jat (value : Lean.Json) (path : List String) : Lean.Json :=
  path.foldl (fun value key => (value.getObjVal? key).toOption.getD .null) value

def strOf (value : Lean.Json) : Option String := match value with | .str text => some text | _ => none

def setCookies (reply : LeanApi.Test.Reply) : List String :=
  (reply.headers.filter (·.1 == "set-cookie")).map (·.2)

def cookieValue (reply : LeanApi.Test.Reply) (name : String) : Option String :=
  (setCookies reply).findSome? fun line =>
    match ((line.splitOn ";").headD "").splitOn "=" with
    | [key, value] => if key == name then some value else none
    | _ => none

def password := "correct horse battery staple"
def origin := "http://127.0.0.1:8080"
def tokenAccept : List (String × String) := [("Accept", "application/vnd.leanapp.token")]
def bearerAuth (token : String) : List (String × String) := [("Authorization", "Bearer " ++ token)]
def signUpBody (name email : String) : String :=
  (Lean.Json.mkObj [("name", .str name), ("email", .str email), ("password", .str password)]).compress
def signInBody (email : String) : String :=
  (Lean.Json.mkObj [("email", .str email), ("password", .str password)]).compress
/-- Times go over the wire as RFC 3339 (decision 15); `date` is seconds after the epoch. -/
def hostBody (title : String) (date : Nat) : String :=
  let minutes := date / 60
  let seconds := date % 60
  let two := fun (n : Nat) => if n < 10 then s!"0{n}" else toString n
  (Lean.Json.mkObj [("title", .str title), ("date", .str s!"1970-01-01T00:{two minutes}:{two seconds}Z")]).compress
/-- The `{"error": …}` of a reply (decision 5). -/
def errorOf (reply : LeanApi.Test.Reply) : Option String := strOf (jat (jsonOf reply) ["error"])
def codeOf (reply : LeanApi.Test.Reply) : Option String := reply.header? "x-leanapp-error"

def checks (svc : LeanApi.Service) (clock : System.FilePath) : CheckM Unit := do
  let request := fun (method target : String) (headers : List (String × String)) (body : String) =>
    (LeanApi.Test.request svc method target headers body : IO LeanApi.Test.Reply)
  -- Exact allowlist: the five listed entries, in order, with their own methods and templates.
  let manifest ← request "GET" "/api/manifest" [] ""
  let ops := match jat (jsonOf manifest) ["operations"] with | .arr ops => ops.toList | _ => []
  expect (ops.map (fun op => strOf (jat op ["name"])) ==
    [some "signUp", some "signIn", some "host", some "partyTitle", some "rsvp"])
    "manifest lists exactly the routed operations"
  expect (ops.map (fun op => (strOf (jat op ["http", "method"]), strOf (jat op ["http", "path"]))) ==
    [(some "POST", some "/sign-up"), (some "POST", some "/sign-in"), (some "POST", some "/parties"),
     (some "GET", some "/parties/:party"), (some "POST", some "/parties/:party/rsvp")])
    "manifest carries each route's method and template"
  expect (jat (ops.getD 4 .null) ["http", "params"] == .arr #[.str "party"]) "manifest names path parameters"
  expect ((manifest.body.splitOn "\"cancel\"").length == 1) "unlisted operation absent from manifest"
  -- Unlisted operations and the milestone 1 name-derived paths are not routable.
  for target in ["/api/routechecks/cancel", "/api/routechecks/rsvp", "/api/routechecks/signUp", "/parties/1/cancel"] do
    expect ((← request "POST" target [] "{}").status == 404) s!"not routable: {target}"
  -- curl-style sign-up: no Origin, no cookie, explicit token request.
  let asha ← request "POST" "/sign-up" tokenAccept (signUpBody "Asha" "asha@example.com")
  expect (asha.status == 200 && (jat (jsonOf asha) ["ok"]) != .null) "token sign-up succeeds without Origin"
  let some ashaToken := strOf (jat (jsonOf asha) ["ok", "token"]) | do expect false "token sign-up returns a token"; return
  expect ((jat (jsonOf asha) ["ok", "profile"]) == (1 : Nat)) "token reply carries the profile ref (a bare integer)"
  expect ((setCookies asha).isEmpty && asha.header? "x-leanapp-auth-csrf" == none) "token reply sets no cookie and no CSRF"
  expect (asha.header? "cache-control" == some "private, no-store") "token reply is not stored"
  let ben ← request "POST" "/sign-up" tokenAccept (signUpBody "Ben" "ben@example.com")
  let some benToken := strOf (jat (jsonOf ben) ["ok", "token"]) | do expect false "second token sign-up"; return
  -- Bearer commands need neither CSRF nor Origin.
  let party ← request "POST" "/parties" (bearerAuth ashaToken) (hostBody "Housewarming" 500)
  expect (party.status == 200) "bearer host succeeds without CSRF or Origin"
  let some key := (match jat (jsonOf party) ["ok"] with | .num n => some (toString n) | _ => none) | do expect false "party reference"; return
  let rsvped ← request "POST" s!"/parties/{key}/rsvp" (bearerAuth benToken) ""
  expect (rsvped.status == 200 && rsvped.body == "{\"ok\":null}") "bearer RSVP through a path parameter"
  let again ← request "POST" s!"/parties/{key}/rsvp" (bearerAuth benToken) "{}"
  expect (again.status == 200) "empty-object body binds the path parameter"
  -- GET through the path; anonymous viewer allowed, curl's Accept reaches the endpoint.
  let title ← request "GET" s!"/parties/{key}" [("Accept", "*/*")] ""
  expect (title.status == 200 && title.body == "{\"ok\":\"Housewarming\"}") "GET query binds the path parameter"
  let html ← request "GET" s!"/parties/{key}" [("Accept", "text/html,application/xhtml+xml")] ""
  expect (html.status == 200 && html.body == "<p>party page</p>") "browser navigation on the same path gets the page (the pages hook)"
  let missing ← request "GET" "/parties/999" [] ""
  expect (missing.status == 422 && missing.body == "{\"error\":\"partyMissing\"}") "typed domain error over GET"
  -- Path binding failures.
  expect ((← request "POST" "/parties/abc/rsvp" (bearerAuth benToken) "").status == 400) "invalid path identifier is a decode failure"
  let duplicate ← request "POST" s!"/parties/{key}/rsvp" (bearerAuth benToken)
    (Lean.Json.mkObj [("party", jat (jsonOf party) ["ok"])]).compress
  expect (duplicate.status == 400 && errorOf duplicate == some "badRequest" && codeOf duplicate == some "request.path_field_in_body")
    "body cannot also supply a path field"
  expect ((← request "GET" s!"/parties/{key}/rsvp" [] "").status == 405) "GET on a command route is not routed"
  expect ((← request "GET" s!"/parties/{key}" [] "{\"party\":1}").status == 400) "GET takes no body"
  -- Missing and invalid bearer tokens.
  let anonymous ← request "POST" s!"/parties/{key}/rsvp" [] ""
  expect (anonymous.status == 401 && anonymous.body == "{\"error\":\"unauthorized\"}") "SignedIn route without a credential is 401"
  let unknown ← request "POST" s!"/parties/{key}/rsvp" (bearerAuth (String.ofList (List.replicate 43 'A'))) ""
  expect (unknown.status == 401) "unknown bearer token is 401"
  expect ((← request "POST" s!"/parties/{key}/rsvp" (bearerAuth "short") "").status == 401) "malformed bearer token is 401"
  expect ((← request "POST" s!"/parties/{key}/rsvp" [("Authorization", "Basic " ++ benToken)] "").status == 401) "other scheme is 401"
  expect ((← request "GET" s!"/parties/{key}" (bearerAuth "short") "").status == 401) "invalid bearer never becomes anonymous"
  -- A default (browser) sign-in: cookie only, no token in the body.
  let browser ← request "POST" "/sign-in" [("Origin", origin)] (signInBody "asha@example.com")
  let some session := cookieValue browser "leanapp_session" | do expect false "browser sign-in sets the session cookie"; return
  let some csrf := cookieValue browser "leanapp_csrf" | do expect false "browser sign-in sets the CSRF cookie"; return
  expect (browser.status == 200 && (browser.body.splitOn session).length == 1 && (browser.body.splitOn "token").length == 1)
    "default sign-in never puts the token in the body"
  expect (browser.body == "{\"ok\":1}") "default sign-in body is the profile ref"
  expect ((← request "POST" "/sign-in" [] (signInBody "asha@example.com")).status == 403) "default sign-in still needs Origin"
  -- Decision 9: only token mode lets an anonymous command skip Origin.
  let tokenSignIn ← request "POST" "/sign-in" tokenAccept (signInBody "asha@example.com")
  expect (tokenSignIn.status == 200 && (strOf (jat (jsonOf tokenSignIn) ["ok", "token"])).isSome &&
    (setCookies tokenSignIn).isEmpty) "token sign-in with no Origin succeeds and sets no cookie"
  expect ((← request "POST" "/sign-in" [("Origin", "http://evil.test")] (signInBody "asha@example.com")).status == 403)
    "cookie-mode sign-in with a wrong Origin is refused"
  let noOrigin ← request "POST" "/sign-up" [] (signUpBody "Cleo" "cleo@example.com")
  expect (noOrigin.status == 403 && (setCookies noOrigin).isEmpty) "cookie-mode sign-up with no Origin is refused"
  let wrongOrigin ← request "POST" "/sign-up" [("Origin", "http://evil.test")] (signUpBody "Cleo" "cleo@example.com")
  expect (wrongOrigin.status == 403 && (setCookies wrongOrigin).isEmpty) "cookie-mode sign-up with a wrong Origin is refused"
  let tokenWrongOrigin ← request "POST" "/sign-up" ([("Origin", "http://evil.test")] ++ tokenAccept) (signUpBody "Cleo" "cleo@example.com")
  expect (tokenWrongOrigin.status == 200 && (setCookies tokenWrongOrigin).isEmpty) "token-mode sign-up needs no Origin check"
  let cookie := [("Cookie", s!"leanapp_session={session}; leanapp_csrf={csrf}"), ("Origin", origin)]
  let noCsrf ← request "POST" s!"/parties/{key}/rsvp" cookie ""
  expect (noCsrf.status == 403) "cookie request without CSRF still fails"
  expect ((← request "POST" s!"/parties/{key}/rsvp" (cookie ++ [("x-csrf-token", csrf)]) "").status == 200) "cookie request with CSRF succeeds"
  expect ((← request "POST" s!"/parties/{key}/rsvp" [("Cookie", s!"leanapp_session={session}"), ("x-csrf-token", csrf)] "").status == 403)
    "cookie request without Origin still fails"
  let both ← request "POST" s!"/parties/{key}/rsvp" (cookie ++ [("x-csrf-token", csrf)] ++ bearerAuth benToken) ""
  expect (both.status == 400 && errorOf both == some "badRequest" && codeOf both == some "auth.ambiguous_credentials") "cookie and bearer together are 400"
  expect ((← request "GET" s!"/parties/{key}" (cookie ++ bearerAuth benToken) "").status == 400) "ambiguous credentials on a read are 400"
  -- Revocation: a token sign-in presenting the old bearer rotates it.
  let rotated ← request "POST" "/sign-in" (tokenAccept ++ bearerAuth benToken) (signInBody "ben@example.com")
  let some newToken := strOf (jat (jsonOf rotated) ["ok", "token"]) | do expect false "token sign-in returns a token"; return
  expect (rotated.status == 200 && newToken != benToken && (setCookies rotated).isEmpty) "token sign-in issues a new token"
  expect ((← request "POST" s!"/parties/{key}/rsvp" (bearerAuth benToken) "").status == 401) "revoked bearer session is refused"
  expect ((← request "POST" s!"/parties/{key}/rsvp" (bearerAuth newToken) "").status == 200) "rotated bearer session works"
  let wrong ← request "POST" "/sign-in" tokenAccept
    (Lean.Json.mkObj [("email", .str "ben@example.com"), ("password", .str "wrong password but long")]).compress
  expect (wrong.status == 422 && (wrong.body.splitOn "token").length == 1) "failed token sign-in returns no token"
  -- Expiry: the same exact cutoff as cookies.
  IO.FS.writeFile clock "86499"
  expect ((← request "POST" s!"/parties/{key}/rsvp" (bearerAuth newToken) "").status == 200) "bearer valid before expiry"
  IO.FS.writeFile clock "86500"
  expect ((← request "POST" s!"/parties/{key}/rsvp" (bearerAuth ashaToken) "").status == 401) "expired bearer session is refused"
  IO.FS.writeFile clock "100"

/-- The `Option SignedIn` actor dictionary, resolved in one read snapshot. -/
def optionalActor (context : LeanApi.Native.Context app.Database Person) (env : LeanApi.Env) (req : LeanApi.Req) :
    LeanDb.Read app.Database (Contract.CallResult (Option SignedIn) Empty) :=
  (LeanApi.Native.optionalPrincipalActor (P := Person) inferInstance rfl).resolve (Scope := Unit)
    context.store context.cookies env req false

/-- A page at the path of the GET endpoint, through the `pages` hook a page layer uses. -/
def withPage : LeanApi.Native.NativeApp app.Database Person :=
  { app with pages := fun _ => [{ path := "/parties/:party", handler := fun _ => pure (LeanApi.Res.html "<p>party page</p>") }] }

def run : IO UInt32 := do
  let suffix ← LeanApi.Tokens.generate
  let directory : System.FilePath := ".lake/test-db" / s!"route-checks-{suffix}"
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "clock") "100"
  let config : LeanApi.Native.AppConfig := {
    database := directory / "app.sqlite"
    clockFile := some (directory / "clock") }
  let ((), results) ← withPage.withService config (fun context svc => do
    let ((), results) ← (checks svc (directory / "clock")).run {}
    -- Runtime validation repeats the elaboration checks for hand-built bindings.
    let codecs ← IO.ofExcept (Contract.Http.codecs.mapError fun _ => "codecs")
    let ref : LeanApi.Native.PathField := LeanApi.Native.PathField.of "party" (Ref Party)
    let assemble := fun (binding : LeanApi.Native.RouteBinding) =>
      LeanApi.Native.assembleCommandAt (Actor := fun _ => SignedIn)
        (actorContext := LeanApi.Native.principalActor (P := Person) inferInstance rfl)
        context codecs binding rsvp.operation rsvp.Requirements.infer
    let getCommand := LeanApi.Native.Application.create (s := app.Database)
      [assemble { method := .get, path := "/x/:party", fields := [ref] }]
    let unbound := LeanApi.Native.Application.create (s := app.Database)
      [assemble { path := "/x/:id", fields := [{ ref with name := "id" }] }]
    let codesOf := fun (result : Ontology.Validation (LeanApi.Native.Application app.Database)) =>
      match result with | .error errors => errors.toList.map (·.code) | .ok _ => []
    -- The `Option SignedIn` actor: none without a credential, some with a live bearer,
    -- 401 for a presented invalid one.
    let optional := fun (headers : List (String × String)) => do
      let req : LeanApi.Req := { headers := headers.map fun (k, v) => (k.toLower, v) }
      match ← context.dc.read (LeanDb.Read.runPrepared (do context.fresh) (fun env => optionalActor context env req)) with
      | .ok (.ok (.ok (.ok actor))) => pure (some (actor.map (·.id.key)))
      | .ok (.ok (.ok (.error .unauthenticated))) => pure none
      | _ => throw (IO.userError "optional actor fixture")
    let signIn ← LeanApi.Test.request svc "POST" "/sign-in" tokenAccept (signInBody "asha@example.com")
    let anonymousActor ← optional []
    let signedActor ← optional (bearerAuth ((strOf (jat (jsonOf signIn) ["ok", "token"])).getD ""))
    let invalidActor ← optional (bearerAuth (String.ofList (List.replicate 43 'B')))
    let ((), results) ← (do
      expect (anonymousActor == some none) "Option SignedIn: none without a credential"
      expect (signedActor == some (some "1")) "Option SignedIn: some for a live bearer session"
      expect (invalidActor == none) "Option SignedIn: a presented invalid credential is 401"
      expect (codesOf getCommand == ["http.get_requires_query"]) "runtime: GET binding of a command is refused"
      expect (codesOf unbound == ["http.path_parameter_unbound"]) "runtime: unbound path parameter is refused").run results
    pure ((), results))
  for failure in results.failed do IO.eprintln s!"FAIL: {failure}"
  IO.println s!"Route/bearer checks: {results.passed} passed, {results.failed.length} failed"
  pure (if results.failed.isEmpty then 0 else 1)

end RouteChecks

/-- `routes`: the checks; `routes --serve`: the app on a socket. -/
def RouteChecks.main (args : List String) : IO UInt32 := do
  match args with
  | ["--serve"] => do withPage.serve { database := "route-checks.sqlite" }; pure 0
  | _ => RouteChecks.run
