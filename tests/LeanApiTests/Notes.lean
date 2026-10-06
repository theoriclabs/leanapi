import Notes.App

namespace Tests.Notes

open LeanApi LeanApi.Test Lean

def jstr (r : Reply) (k : String) : Option String := r.json?.bind fun j => (j.getObjValAs? String k).toOption
def jnat (r : Reply) (k : String) : Option Nat := r.json?.bind fun j => (j.getObjValAs? Nat k).toOption

def basicHdr (u p : String) := ("Authorization", "Basic " ++ Base64.encode s!"{u}:{p}".toUTF8)

def login (svc : Service) (u p : String) : IO String := do
  let _ ← postJson svc "/api/users" (Json.mkObj [("name", .str u), ("password", .str p)])
  let r ← request svc "POST" "/api/sessions" [basicHdr u p]
  return (jstr r "token").getD ""

def run : TestM Unit := do
  let db ← Notes.Db.new
  let svc := Notes.service db (fun _ => pure ())
  section_ "notes example" do
    let r ← request svc "POST" "/api/users" [("Content-Type", "application/x-www-form-urlencoded")] "name=carol&password=pw-carol"
    checkEq "register via form" r.status 201
    checkEq "duplicate name 409" (← postJson svc "/api/users" (Json.mkObj [("name", .str "carol"), ("password", .str "xxxx")])).status 409
    let a ← login svc "alice" "pw-alice"
    let b ← login svc "bob" "pw-bob"
    check "tokens issued" (!a.isEmpty && !b.isEmpty && a != b)
    let r ← request svc "POST" "/api/sessions" [basicHdr "alice" "wrong"]
    checkEq "bad login 401" r.status 401
    let r ← request svc "POST" "/api/sessions" [basicHdr "alice" "pw-alice"]
    check "login sets cookie" ((r.header? "set-cookie").any (·.startsWith "sid="))
    let ah := ("Authorization", s!"Bearer {a}")
    let bh := ("Authorization", s!"Bearer {b}")
    let r ← postJson svc "/api/notes" (Json.mkObj [("title", .str "groceries"), ("body", .str "eggs")]) [ah]
    checkEq "create 201" r.status 201
    let id := (jnat r "id").getD 0
    checkEq "etag" (r.header? "etag") (some "\"1\"")
    checkEq "location" (r.header? "location") (some s!"/api/notes/{id}")
    checkEq "empty title 422" (← postJson svc "/api/notes" (Json.mkObj [("title", .str "")]) [ah]).status 422
    checkEq "owner reads" (← get svc s!"/api/notes/{id}" [ah]).status 200
    checkEq "cookie auth reads" (← get svc s!"/api/notes/{id}" [("Cookie", s!"sid={a}")]).status 200
    let other ← get svc s!"/api/notes/{id}" [bh]
    let missing ← get svc "/api/notes/9999" [bh]
    checkEq "other user: same as missing (status)" other.status missing.status
    checkEq "other user: same as missing (body)" other.body missing.body
    checkEq "unauthenticated 401" (← get svc s!"/api/notes/{id}").status 401
    let r ← request svc "PATCH" s!"/api/notes/{id}" [ah, ("Content-Type", "application/json"), ("If-Match", "\"1\"")] "{\"body\":\"eggs, milk\"}"
    checkEq "patch with matching etag" r.status 200
    checkEq "rev advanced" (r.header? "etag") (some "\"2\"")
    let r ← request svc "PATCH" s!"/api/notes/{id}" [ah, ("Content-Type", "application/json"), ("If-Match", "\"1\"")] "{\"body\":\"x\"}"
    checkEq "stale etag 412" r.status 412
    let r ← get svc "/api/notes?per=1&page=1" [ah]
    checkEq "list total" (jnat r "total") (some 1)
    checkEq "bad per 422" (← get svc "/api/notes?per=0" [ah]).status 422
    checkEq "other user cannot delete" (← request svc "DELETE" s!"/api/notes/{id}" [bh]).status 404
    checkEq "owner deletes" (← request svc "DELETE" s!"/api/notes/{id}" [ah]).status 204
    checkEq "gone" (← get svc s!"/api/notes/{id}" [ah]).status 404

  section_ "concurrency: parallel connections, no lost updates" do
    let tok ← login svc "dave" "pw-dave"
    let n := 64
    let tasks ← (List.range n).mapM fun i => IO.asTask (postJson svc "/api/notes"
      (Json.mkObj [("title", .str s!"note {i}")]) [("Authorization", s!"Bearer {tok}")])
    let mut created := 0
    for t in tasks do
      match ← IO.wait t with
      | .ok r => if r.status == 201 then created := created + 1
      | .error _ => pure ()
    checkEq "all creates succeeded" created n
    let r ← get svc "/api/notes?per=100" [("Authorization", s!"Bearer {tok}")]
    checkEq "store has every note" (jnat r "total") (some n)
    let ids ← Notes.read db fun s => (s.notes.filter (·.owner == "dave")).map (·.id)
    checkEq "ids distinct" ids.toList.eraseDups.length n

end Tests.Notes
