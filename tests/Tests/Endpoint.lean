/-
  Typed endpoints (docs/ENDPOINTS.md): compile-time guarantees, pinned with
  `#guard_msgs`, and runtime behaviour through the in-process client.
-/
import Notes.App

namespace Tests.Endpoint

open LeanApi LeanApi.Test Lean Notes

/-! ## Compile time -/

def bump : Writes Nat Nat := fun n => (n + 1, n + 1)
def peek : Reads Nat Nat := fun n => n
def peekAt (_i : Path Nat) : Reads Nat Nat := fun n => n

-- A GET whose handler writes does not build.
/-- error: could not synthesize default value for parameter '_safe' using tactics
---
error: a GET or HEAD endpoint must not change state, but this handler's effect is `writes` or `io`. Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.
⊢ (Handler.effect Nat (Writes Nat Nat)).Safe -/
#guard_msgs (error) in
example : Endpoint Nat := .get "/counter" bump

example : Endpoint Nat := .post "/counter" bump
example : Endpoint Nat := .get "/counter" peek

/-- error: api!: GET /counter/{a}/{b} has 2 path parameter(s), but `Tests.Endpoint.peekAt` takes 1 `Path` argument(s):
  Path Nat → Reads Nat Nat -/
#guard_msgs (error) in
example : Api Nat := api! [.get "/counter/{a}/{b}" peekAt]

/-- error: api!: invalid routes:
  GET /counter/{a} conflicts with GET /counter/{b} -/
#guard_msgs (error) in
example : Api Nat := api! [.get "/counter/{a}" peekAt, .get "/counter/{b}" peekAt]

/-- An error status is 4xx/5xx by type: a 200 "error" does not typecheck. -/
example : ∀ s : ErrorStatus, s.1 ≠ 200 := fun s h => by have := s.2.1; omega

/-- The effect and inputs come from the signature. -/
example : (Handler.effect (σ := State) (τ := type_of% editNote)) = .writes := rfl
example : (Handler.effect (σ := State) (τ := type_of% getNote)) = .reads := rfl
example : (Handler.pathArity (σ := State) (τ := type_of% editNote)) = 1 := rfl

/-! ## Runtime -/

def run : TestM Unit := do
  section_ "typed endpoints" do
    let db ← Notes.Db.new
    let svc := Notes.service db (fun _ => pure ())
    let _ ← postJson svc "/api/users" (Json.mkObj [("name", .str "erin"), ("password", .str "pw-erin")])
    let r ← request svc "POST" "/api/sessions"
      [("Authorization", "Basic " ++ Base64.encode "erin:pw-erin".toUTF8)]
    let tok := (r.json?.bind fun j => (j.getObjValAs? String "token").toOption).getD ""
    let ah := ("Authorization", s!"Bearer {tok}")
    -- every invalid field across parameters is reported at once
    let r ← request svc "PATCH" "/api/notes/1" [ah, ("Content-Type", "application/json"), ("If-Match", "\"x\"")]
      "{\"title\":\"\"}"
    checkEq "422 across parameters" r.status 422
    let body := r.body
    check "names the header" ((body.splitOn "header.if-match").length > 1)
    check "names the body field" ((body.splitOn "body.title").length > 1)
    checkEq "wrong content type 415" (← request svc "POST" "/api/notes" [ah, ("Content-Type", "text/plain")] "x").status 415
    checkEq "unparseable JSON 400" (← request svc "POST" "/api/notes" [ah, ("Content-Type", "application/json")] "{").status 400
    checkEq "auth before validation" (← request svc "POST" "/api/notes" [("Content-Type", "text/plain")] "x").status 401
    let d := Notes.api.describe
    check "describe shows the signature" ((d.splitOn "Auth User → Path NoteId → IfMatch Rev → Body NoteEdit").length > 1)
    check "describe shows the effect" ((d.splitOn "PATCH /notes/{id:nat} [writes").length > 1)

end Tests.Endpoint
