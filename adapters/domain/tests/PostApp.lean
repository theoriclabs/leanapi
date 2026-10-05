import tests.domain.PostPart1
import LeanApiDomain.App
import LeanApi.Runtime.TestClient

/-! The Part 1 post's operations (LeanReact's `PostPart1`: plain `def`s returning `Op`/`ReadOp`,
`deriving Entity`, `constraint`, `deriving Principal`, an authored `Credential`, `signUp` and
`signIn`) served by the native runtime over SQLite, in the `{"ok": …}` / `{"error": …}`
envelope with bare-integer refs and RFC 3339 times.

- Authentication is the post's own code: `authentication := Person with Credential` declares
  the authored credential entity; `signUp`/`signIn` run with their KDF steps prepared before
  writer admission (`FlowMetadata.kdf`), under `KDFGate`.
- Decision 8 is the post's own `constraint Rsvp.cancelWithParty : cascade party`.
- The post's whole `api` is served with `api := api` (`getParty`'s guest list is the native join
  `Rsvp ⋈ Person`); `edit` and a few extra plain operations are routed explicitly. -/

section SmallApi
open LeanApp.Domain

inductive TitleError where
  | notFound

def partyTitle (session : Option _root_.SignedIn) (party : Ref Party) : ReadOp TitleError Title := do
  let some p ← Party.find party | throw .notFound
  return p.title

inductive RetitleError where
  | notFound
  | notHost

def retitle (me : _root_.SignedIn) (party : Ref Party) (title : Title) : Op RetitleError Unit := do
  let some p ← Party.find party | throw .notFound
  let ⟨_⟩ ← require (me.id == p.host) .notHost
  Party.patch p { title, description := p.description, guestList := p.guestList }

def partyCount (session : Option _root_.SignedIn) : ReadOp Empty Nat := do
  return (← Party.select).length

def smallApi : Api := [
  get  "/parties/:party/title"  partyTitle,
  post "/parties/:party/title"  retitle,
  get  "/party-count"           partyCount
]
end SmallApi

app% PostApp where
  authentication := Person with Credential
  routes := [
    post "/parties/:party/edit" edit.operation,
    get  "/parties/:party/title" partyTitle.operation,
    post "/parties/:party/title" retitle.operation,
    get  "/party-count" partyCount.operation
  ]
  pages := []
  api := api

namespace PostAppChecks

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
def ok (reply : LeanApi.Test.Reply) : Lean.Json := jat (jsonOf reply) ["ok"]
def setCookies (reply : LeanApi.Test.Reply) : List String :=
  (reply.headers.filter (·.1 == "set-cookie")).map (·.2)

def password := "correct horse battery staple"
def origin := "http://127.0.0.1:8080"
def tokenAccept : List (String × String) := [("Accept", "application/vnd.leanapp.token")]
def bearerAuth (token : String) : List (String × String) := [("Authorization", "Bearer " ++ token)]
def obj (fields : List (String × Lean.Json)) : String := (Lean.Json.mkObj fields).compress
def signUpBody (name email : String) : String :=
  obj [("name", .str name), ("email", .str email), ("password", .str password)]
def signInBody (email pass : String) : String := obj [("email", .str email), ("password", .str pass)]

def sqlite (database : System.FilePath) (statement : String) : IO String := do
  let out ← IO.Process.output { cmd := "python3", args := #["-c",
    "import sqlite3,sys; c=sqlite3.connect(sys.argv[1]); r=c.execute(sys.argv[2]).fetchall(); c.commit(); print(r)",
    database.toString, statement] }
  return out.stdout.trimAscii.toString

def runs (context : LeanApi.Domain.Context PostApp.Database Person) : IO Nat :=
  match context.kdf.runs with
  | some counter => counter.atomically get
  | none => pure 0

def checks (context : LeanApi.Domain.Context PostApp.Database Person) (svc : LeanApi.Service)
    (database : System.FilePath) : CheckM Unit := do
  let request := fun (method target : String) (headers : List (String × String)) (body : String) =>
    (LeanApi.Test.request svc method target headers body : IO LeanApi.Test.Reply)
  let manifest ← request "GET" "/api/manifest" [] ""
  let ops := match jat (jsonOf manifest) ["operations"] with | .arr ops => ops.toList | _ => []
  expect (ops.map (fun op => (strOf (jat op ["name"]), strOf (jat op ["http", "method"]), strOf (jat op ["http", "path"]))) ==
    [(some "edit", some "POST", some "/parties/:party/edit"), (some "partyTitle", some "GET", some "/parties/:party/title"),
     (some "retitle", some "POST", some "/parties/:party/title"), (some "partyCount", some "GET", some "/party-count"),
     (some "signUp", some "POST", some "/sign-up"), (some "signIn", some "POST", some "/sign-in"),
     (some "hostParty", some "POST", some "/parties"), (some "getParty", some "GET", some "/parties/:party"),
     (some "rsvp", some "POST", some "/parties/:party/rsvp"), (some "cancel", some "POST", some "/parties/:party/cancel")])
    "manifest: the routed operations, then the post's `api` in order"
  -- The post's signUp in token mode (decision 9: no Origin): {"ok": {"profile": 1, "token": …}}.
  let before ← runs context
  let asha ← request "POST" "/sign-up" tokenAccept (signUpBody "Asha" "asha@example.com")
  expect (asha.status == 200 && jat (ok asha) ["profile"] == (1 : Nat) && (setCookies asha).isEmpty)
    "authored signUp: token reply, profile ref 1, no cookie"
  expect ((← runs context) == before + 1) "signUp: one KDF run (Password.hash, prepared)"
  let some ashaToken := strOf (jat (ok asha) ["token"]) | do expect false "sign-up token"; return
  let ben ← request "POST" "/sign-up" tokenAccept (signUpBody "Ben" "ben@example.com")
  let some benToken := strOf (jat (ok ben) ["token"]) | do expect false "second sign-up token"; return
  expect ((← request "POST" "/sign-up" [] (signUpBody "Cleo" "cleo@example.com")).status == 403)
    "cookie-mode sign-up without Origin is refused"
  let taken ← request "POST" "/sign-up" tokenAccept (signUpBody "Not Asha" "ASHA@example.com")
  expect (taken.status == 422 && taken.body == "{\"error\":\"emailTaken\"}") "duplicate email: {\"error\":\"emailTaken\"}"
  expect ((← sqlite database "SELECT count(*) FROM person") == "[(2,)]" &&
    (← sqlite database "SELECT count(*) FROM credential") == "[(2,)]") "a refused sign-up writes nothing"
  -- Decision 2: an unknown email and a wrong password: same bytes, same KDF work.
  let r0 ← runs context
  let t0 ← IO.monoMsNow
  let unknown ← request "POST" "/sign-in" tokenAccept (signInBody "nobody@example.com" password)
  let t1 ← IO.monoMsNow
  let r1 ← runs context
  let wrong ← request "POST" "/sign-in" tokenAccept (signInBody "asha@example.com" "wrong password but long")
  let t2 ← IO.monoMsNow
  let r2 ← runs context
  expect (unknown.status == 422 && unknown.status == wrong.status && unknown.body == wrong.body &&
    unknown.body == "{\"error\":\"wrongEmailOrPassword\"}") "unknown email and wrong password: identical bytes"
  expect (r1 == r0 + 1 && r2 == r1 + 1) "unknown email and wrong password: one KDF run each"
  IO.println s!"timing: unknown email {t1 - t0} ms, wrong password {t2 - t1} ms"
  expect ((t1 - t0) * 4 ≥ (t2 - t1) && (t2 - t1) * 4 ≥ (t1 - t0)) "comparable sign-in time (within 4x)"
  -- Sign-in rotates the presented session; the default (cookie) reply has no token.
  let rotated ← request "POST" "/sign-in" (tokenAccept ++ bearerAuth benToken) (signInBody "ben@example.com" password)
  let some benNext := strOf (jat (ok rotated) ["token"]) | do expect false "token sign-in"; return
  let browser ← request "POST" "/sign-in" [("Origin", origin)] (signInBody "asha@example.com" password)
  expect (browser.status == 200 && browser.body == "{\"ok\":1}" && (setCookies browser).length == 2)
    "cookie sign-in: {\"ok\":1}, session and CSRF cookies, no token in the body"
  -- Envelope and wire values: bare-integer refs, RFC 3339 times, unauthorized.
  let partyBody := fun (date : String) => obj [("title", .str "Housewarming"), ("description", .str "Bring a plant"),
    ("date", .str date), ("guestList", .str "everyone")]
  let party ← request "POST" "/parties" (bearerAuth ashaToken) (partyBody "1970-01-01T00:08:20Z")
  expect (party.status == 200 && party.body == "{\"ok\":1}") "hostParty: {\"ok\":1}"
  expect ((← request "POST" "/parties/1/rsvp" (bearerAuth benToken) "").status == 401) "rotated session refused"
  let past ← request "POST" "/parties" (bearerAuth ashaToken) (partyBody "1970-01-01T00:00:50Z")
  expect (past.status == 422 && past.body == "{\"error\":\"dateInPast\"}") "Clock.now + require: dateInPast"
  let anonymous ← request "POST" "/parties/1/rsvp" [] ""
  expect (anonymous.status == 401 && anonymous.body == "{\"error\":\"unauthorized\"}") "no credential: {\"error\":\"unauthorized\"}"
  let rsvp ← request "POST" "/parties/1/rsvp" (bearerAuth benNext) ""
  expect (rsvp.status == 200 && rsvp.body == "{\"ok\":null}") "rsvp with bearer: {\"ok\":null}"
  expect ((← request "POST" "/parties/1/rsvp" (bearerAuth benNext) "").status == 200 &&
    (← sqlite database "SELECT count(*) FROM rsvp") == "[(1,)]") "second RSVP: the onePerGuest conflict is a value"
  expect ((← request "POST" "/parties/9/rsvp" (bearerAuth benNext) "").body == "{\"error\":\"notFound\"}") "rsvp: notFound"
  -- getParty: a GET ReadOp, Option SignedIn, Viewer.of through Rsvp.findBy, the native join.
  let page ← request "GET" "/parties/1" [] ""
  expect (page.status == 200 && page.body ==
    "{\"ok\":{\"date\":\"1970-01-01T00:08:20Z\",\"description\":\"Bring a plant\",\"guests\":{\"tag\":\"visible\",\"value\":{\"guests\":[{\"name\":\"Ben\"}]}},\"title\":\"Housewarming\"}}")
    "getParty: the native guest join, RFC 3339 date"
  expect ((← request "GET" "/parties/1" (bearerAuth "short") "").status == 401) "getParty: an invalid bearer is 401"
  expect ((← request "GET" "/parties/9" [] "").body == "{\"error\":\"notFound\"}") "getParty: notFound"
  let title ← request "GET" "/parties/1/title" [] ""
  expect (title.status == 200 && title.body == "{\"ok\":\"Housewarming\"}") "GET ReadOp, anonymous Option SignedIn"
  let edit ← request "POST" "/parties/1/edit" (bearerAuth ashaToken)
    (obj [("changes", .mkObj [("title", .str "Garden party"), ("description", .str "Bring a plant"),
      ("guestList", .str "hostOnly")])])
  expect (edit.status == 200) "edit with Party.Changes (Party.patch)"
  let hiddenToGuest ← request "GET" "/parties/1" (bearerAuth benNext) ""
  expect ((hiddenToGuest.body.splitOn "\"hidden\"").length == 2 && (hiddenToGuest.body.splitOn "Ben").length == 1)
    "hostOnly: an attendee sees `hidden`, and no name leaves the server"
  expect (((← request "GET" "/parties/1" (bearerAuth ashaToken) "").body.splitOn "\"Ben\"").length == 2)
    "hostOnly: the host sees the guest names"
  let notHost ← request "POST" "/parties/1/title" (bearerAuth benNext) (obj [("title", .str "Mine")])
  expect (notHost.status == 422 && notHost.body == "{\"error\":\"notHost\"}") "retitle: notHost"
  expect ((← request "POST" "/parties/1/title" (bearerAuth ashaToken) (obj [("title", .str "Picnic")])).status == 200 &&
    (← request "GET" "/parties/1/title" [] "").body == "{\"ok\":\"Picnic\"}") "retitle by the host"
  expect ((← request "GET" "/party-count" [] "").body == "{\"ok\":1}") "partyCount through Party.select: a bare number"
  -- Decision 8: cancelling a party deletes its RSVPs; people stay.
  let party2 ← request "POST" "/parties" (bearerAuth ashaToken) (partyBody "1970-01-01T00:11:40Z")
  expect (party2.body == "{\"ok\":2}") "a second party"
  discard <| request "POST" "/parties/2/rsvp" (bearerAuth benNext) ""
  expect ((← request "POST" "/parties/2/cancel" (bearerAuth benNext) "").body == "{\"error\":\"notHost\"}") "cancel: notHost"
  expect ((← request "POST" "/parties/2/cancel" (bearerAuth ashaToken) "").body == "{\"ok\":null}") "cancel by the host"
  expect ((← sqlite database "SELECT count(*) FROM rsvp WHERE party = 2") == "[(0,)]" &&
    (← sqlite database "SELECT count(*) FROM person") == "[(2,)]") "the cascade removed its RSVPs, people stay"
  let unknownRoute ← request "GET" "/nowhere" [] ""
  expect (unknownRoute.status == 404 && unknownRoute.body == "{\"error\":\"notFound\"}") "unknown route: {\"error\":\"notFound\"}"
  let both ← request "POST" "/parties/1/rsvp" (bearerAuth benNext ++ [("Cookie", "leanapp_session=" ++ String.ofList (List.replicate 43 'A'))]) ""
  expect (both.status == 400 && both.body == "{\"error\":\"badRequest\"}" &&
    both.header? "x-leanapp-error" == some "auth.ambiguous_credentials") "cookie and bearer: badRequest (code in a header)"
  -- Sign-up is atomic: a session insert that fails after the person and credential rows rolls
  -- both back.
  discard <| sqlite database "ALTER TABLE session RENAME TO session_hold"
  let failed ← request "POST" "/sign-up" tokenAccept (signUpBody "Dev" "dev@example.com")
  discard <| sqlite database "ALTER TABLE session_hold RENAME TO session"
  expect (failed.status == 500 || failed.status == 503) "late session failure is a framework failure"
  expect ((← sqlite database "SELECT count(*) FROM person WHERE email='dev@example.com'") == "[(0,)]" &&
    (← sqlite database "SELECT count(*) FROM credential") == "[(2,)]") "sign-up atomic: no person or credential left"
  -- The KDF never runs under the writer: with the writer held outside, sign-up's KDF completes
  -- while the request still waits for admission.
  let holder ← IO.Process.spawn { cmd := "python3", stdin := .piped, stdout := .piped, args := #["-u", "-c",
    "import sqlite3,sys\nc=sqlite3.connect(sys.argv[1]); c.execute('BEGIN IMMEDIATE'); print('held', flush=True); sys.stdin.readline(); c.commit()",
    database.toString] }
  let held ← holder.stdout.getLine
  let kdfBefore ← runs context
  let pending ← IO.asTask (request "POST" "/sign-up" tokenAccept (signUpBody "Eve" "eve@example.com")) .dedicated
  let mut kdfDone := false
  for _ in [0:200] do
    if (← runs context) > kdfBefore then
      kdfDone := true
      break
    IO.sleep 20
  IO.sleep 200
  let waiting := !(← IO.hasFinished pending)
  let (stdin, child) ← holder.takeStdin
  stdin.putStrLn ""
  stdin.flush
  discard <| child.wait
  let done ← IO.ofExcept (← IO.wait pending)
  expect (held.trimAscii.toString == "held" && kdfDone && waiting) "KDF completed while the writer was held elsewhere"
  expect (done.status == 200) "the request was admitted once the writer was free"

def run : IO UInt32 := do
  let suffix ← LeanApi.Tokens.generate
  let directory : System.FilePath := ".lake/test-db" / s!"post-app-{suffix}"
  IO.FS.createDirAll directory
  IO.FS.writeFile (directory / "clock") "100"
  let config : LeanApi.Domain.AppConfig := {
    database := directory / "post.sqlite"
    clockFile := some (directory / "clock") }
  let ((), results) ← PostApp.withService config fun context svc =>
    (checks context svc (directory / "post.sqlite")).run {}
  for failure in results.failed do IO.eprintln s!"FAIL: {failure}"
  IO.println s!"Post app checks: {results.passed} passed, {results.failed.length} failed"
  pure (if results.failed.isEmpty then 0 else 1)

end PostAppChecks

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => PostAppChecks.run
  | ["serve"] => PostApp.main [] { database := "post.sqlite" }
  | _ => PostApp.main args { database := "post.sqlite" }
