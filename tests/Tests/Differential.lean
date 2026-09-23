/-
  Differential check: the native service (LeanDB, scoped repository,
  single writer) against the reference model `step`, on random request
  sequences. The model is given the same sessions and players; each request
  goes to both, and statuses, bodies and the headers that matter must agree.
  Evidence for "native ≡ model" in EVIDENCE.md (checked, not proved).
-/
import PrivateGames.Model.Step
import PrivateGames.Api
import PrivateGames.App.Service
import Tests.Games

namespace Tests.Differential

open LeanApi LeanApi.Test Lean PrivateGames PrivateGames.App PrivateGames.Model Tests.Games

/-- Compare responses on what is observable and deterministic. -/
def comparable (r : Res) : Nat × List (String × String) × String :=
  (r.status, r.headers.filter (fun (k, _) => k == "etag" || k == "location" || k == "idempotent-replayed" || k == "allow" || k == "www-authenticate"),
   r.bodyText)

def replyComparable (r : Reply) : Nat × List (String × String) × String :=
  (r.status, r.headers.filter (fun (k, _) => k == "etag" || k == "location" || k == "idempotent-replayed" || k == "allow" || k == "www-authenticate"),
   r.body)

/-! ## Requests as data

A probe is a typed call plus at most one fault. Faults are applied while
rendering (a header is left out, a value is replaced), never by inspecting
rendered strings, and each call lists the faults that apply to it. -/

/-- A call to the game API, with typed fields. -/
inductive Call where
  | openGame (opponent : Nat) (key : Option Nat)
  | readGame (gid : Nat)
  | listGames (page per : Nat)
  | playMove (gid rev cell : Nat) (key : Option Nat)
  | resign (gid : Nat) (key : Option Nat)
  /-- A method the route does not allow (405). -/
  | wrongMethod (gid : Nat)

/-- One malformation, for one error path. -/
inductive Fault where
  | noCredentials      -- 401
  | unknownToken       -- 401
  | noIfMatch          -- 428
  | wrongContentType   -- 415
  | invalidKey         -- 422
  | pageZero           -- 422
  deriving BEq, Repr

/-- The faults that make sense for a call. -/
def Call.faults : Call → List Fault
  | .openGame .. => [.noCredentials, .unknownToken, .wrongContentType, .invalidKey]
  | .readGame _ | .wrongMethod _ => [.noCredentials, .unknownToken]
  | .listGames .. => [.noCredentials, .unknownToken, .pageZero]
  | .playMove .. => [.noCredentials, .unknownToken, .noIfMatch, .wrongContentType, .invalidKey]
  | .resign .. => [.noCredentials, .unknownToken, .invalidKey]

structure Probe where
  call : Call
  fault : Option Fault := none

/-- What goes on the wire. -/
structure Wire where
  method : Method
  target : String
  headers : List (String × String)
  body : String := ""

def jsonBody (fields : List (String × Json)) : String := (Json.mkObj fields).compress

/-- Render a probe for the caller holding `token`. -/
def Probe.render (p : Probe) (token : String) : Wire :=
  let has (f : Fault) := p.fault == some f
  let auth := if has .noCredentials then []
    else [("Authorization", s!"Bearer {if has .unknownToken then "bogus" else token}")]
  let contentType := [("Content-Type", if has .wrongContentType then "text/plain" else "application/json")]
  let key (k : Option Nat) := if has .invalidKey then [("Idempotency-Key", "bad key")]
    else (k.map fun k => [("Idempotency-Key", s!"k{k}")]).getD []
  match p.call with
  | .openGame opp k => ⟨.post, "/games", auth ++ contentType ++ key k, jsonBody [("opponent", Json.num opp)]⟩
  | .readGame gid => ⟨.get, s!"/games/{gid}", auth, ""⟩
  | .listGames page per => ⟨.get, s!"/games?per={per}&page={if has .pageZero then 0 else page}", auth, ""⟩
  | .playMove gid rev cell k =>
    let ifMatch := if has .noIfMatch then [] else [("If-Match", s!"\"{rev}\"")]
    ⟨.post, s!"/games/{gid}/moves", auth ++ contentType ++ ifMatch ++ key k, jsonBody [("cell", Json.num cell)]⟩
  | .resign gid k => ⟨.post, s!"/games/{gid}/resignation", auth ++ key k, ""⟩
  | .wrongMethod gid => ⟨.put, s!"/games/{gid}", auth, ""⟩

def Wire.toReq (w : Wire) : Req :=
  Req.mk' w.method w.target (w.headers.map fun (k, v) => (k.toLower, v)) w.body.toUTF8

/-- A random probe: a call over a few games and users, and on some calls
    one of its applicable faults. -/
def randomProbe (opponents : Array Nat) : IO Probe := do
  let gid ← IO.rand 1 6
  let key ← do let k ← IO.rand 0 3; pure (if k == 0 then none else some k)
  let call ← match ← IO.rand 0 8 with
    | 0 | 1 => pure (Call.openGame opponents[← IO.rand 0 (opponents.size - 1)]! key)
    | 2 => pure (.readGame gid)
    | 3 => pure (.listGames (1 + gid % 3) 2)
    | 4 | 5 | 6 => pure (.playMove gid (← IO.rand 0 3) (← IO.rand 0 8) key)
    | 7 => pure (.resign gid key)
    | _ => pure (.wrongMethod gid)
  let fs := call.faults
  let fault ← do
    let i ← IO.rand 0 (2 * fs.length)
    pure fs[i]?
  return { call, fault }

def run : TestM Unit := do
  section_ "differential: native vs model" do
    let env ← freshEnv "differential"
    let names := ["n1", "n2", "n3", "n4"]
    let mut users : Array (Nat × String) := #[]
    for n in names do users := users.push (← signup env.svc n)
    let mut world : World := {
      games := [], receipts := [], nextGame := 1
      players := users.toList.map fun (id, _) => ⟨id⟩
      sessions := users.toList.map fun (id, t) => (Tokens.digest t, ⟨id⟩) }
    let mut typedWorld := world
    let mut mismatches := 0
    let mut typedMismatches := 0
    let mut total := 0
    let mut seen : List Nat := []
    for step_ in [0:400] do
      let (_, tok) := users[← IO.rand 0 (users.size - 1)]!
      let probe ← randomProbe (users.map (·.1))
      let wire := probe.render tok
      let native ← request env.svc (toString wire.method) wire.target wire.headers wire.body
      let req := wire.toReq
      let (res, w') := Model.step req world
      world := w'
      let (tres, tw') := PrivateGames.Api.gamesApi.step {} req typedWorld
      typedWorld := tw'
      total := total + 1
      unless seen.contains res.status do seen := res.status :: seen
      if comparable tres != comparable res then
        typedMismatches := typedMismatches + 1
        if typedMismatches ≤ 3 then
          IO.eprintln s!"  step {step_}: {wire.method} {wire.target} {repr probe.fault}\n    typed  {repr (comparable tres)}\n    model  {repr (comparable res)}"
      if replyComparable native != comparable res then
        mismatches := mismatches + 1
        if mismatches ≤ 3 then
          IO.eprintln s!"  step {step_}: {wire.method} {wire.target} {repr probe.fault}\n    native {repr (replyComparable native)}\n    model  {repr (comparable res)}"
    checkEq s!"{total} requests: native ≡ model" mismatches 0
    checkEq s!"{total} requests: typed API ≡ model" typedMismatches 0
    for code in [200, 201, 401, 404, 405, 409, 412, 415, 422, 428] do
      check s!"status {code} exercised" (seen.contains code)
    env.rt.close

end Tests.Differential
