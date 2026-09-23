/-
  The native service (M5): operation → route bindings over the scoped
  repository.

  Request path for a proved route (DESIGN §3.3):
    resolve (shared `resolveIn`) → authenticate (bearer digest → player)
    → decode (pure, shared) → load `Need` via the scoped repository
    → `core` (pure, shared) → commit plan (CAS + receipt, one transaction)
    → response.

  Unproved routes: `POST /players` (register) and `POST /sessions` (login)
  are plain M1 handlers. They touch only player/token tables, never games
  or receipts, and are listed as outside the proved set in EVIDENCE.md.
-/
import PrivateGames.Storage.Repo

namespace PrivateGames.App

open LeanApi Lean PrivateGames.Storage

def repoErrRes : RepoError → Res
  | .notFound => hidden
  | .conflict => ((Problem.make 412 (some "the game has changed"))).toRes
  | .keyReused => keyReused
  | .busy => ((Problem.make 503 (some "server busy")).withHeader "retry-after" "1").toRes
  | .corrupt _ => (Problem.make 500).toRes
  | .db _ => (Problem.make 500).toRes

/-- Load what the core needs through the scoped repository. -/
def load (repo : Repo) (p : PlayerId) (n : Need) : IO (Except RepoError Slice) := do
  let game ← match n.game with
    | some gid => repo.loadVisible p gid
    | none => pure (.ok none)
  let page ← match n.page with
    | some (off, lim) => repo.listVisible p off lim
    | none => pure (.ok ([], 0))
  let receipt ← match n.receipt with
    | some (op, key) => repo.receipt p op key
    | none => pure (.ok none)
  let exists_ ← match n.player with
    | some q => repo.playerExists q
    | none => pure (.ok false)
  return do return { game := ← game, page := ← page, receipt := ← receipt, playerExists := ← exists_ }

def runPlan (repo : Repo) (p : PlayerId) : Plan → IO Res
  | .respond r => pure r
  | .write w k build => do
    match ← repo.commit p w k build with
    | .ok (res, _) => pure res
    | .error e => pure (repoErrRes e)

/-- One proved operation, natively. -/
def operation (repo : Repo) (op : Op) : App := fun req => do
  match authDigest req with
  | .error r => return r
  | .ok d =>
    match ← repo.tokenPlayer d with
    | .error e => return repoErrRes e
    | .ok none => return unknownToken
    | .ok (some p) =>
      match decode op req with
      | .error r => return r
      | .ok i =>
        match ← load repo p i.need with
        | .error e => return repoErrRes e
        | .ok s => runPlan repo p (core p i s)

/-! ## Unproved routes: accounts -/

structure Creds where
  name : String
  password : String

def credsJson : Extract Creds := fun r => do
  let j ← Extract.rawJson r
  let (n, p) ← both (field "body" j "name") (field "body" j "password")
  return ⟨n, p⟩

def accountRoutes (repo : Repo) (dummy : String) (params : LeanCrypto.Password.Params) : List Route := [
  Route.post "/players" (handleJson credsJson fun c => do
    if c.name.isEmpty || c.name.length > 64 || c.password.length < 8 then
      return (FieldError.problem [⟨"body", "name 1–64 characters, password at least 8"⟩]).toRes
    let h ← LeanCrypto.Password.hash c.password params
    match ← repo.createPlayer c.name h with
    | .ok p => return Res.created (Json.mkObj [("id", Json.num p.n), ("name", .str c.name)])
    | .error .conflict => return (Problem.conflict "name taken").toRes
    | .error e => return repoErrRes e),
  Route.post "/sessions" (requireAuth
    (basicWithPasswords (fun u => do
        match ← repo.playerByName u with
        | .ok r => return r
        | .error _ => return none) dummy "games")
    fun p _ => do
      let tok ← Tokens.generate
      match ← repo.addToken (Tokens.digest tok) p with
      | .ok () => return Res.created (Json.mkObj [("token", .str tok), ("player", Json.num p.n)])
      | .error e => return repoErrRes e)
]

/-- The whole route table: proved operations plus accounts. -/
def routes (repo : Repo) (dummy : String) (params : LeanCrypto.Password.Params := {}) : List Route :=
  (routeTable.map fun (op, m, t) =>
    ({ method := m, template := t, handler := operation repo op, name := some op.name,
       bodyLimit := 16 * 1024 } : Route))
  ++ accountRoutes repo dummy params

def stack (log : String → IO Unit := IO.eprintln) (ready : IO Bool := pure true) : Stack := Stack.of [
  recover log, requestId, accessLog log, health ready, securityHeaders, timeout 10000]

def service (repo : Repo) (dummy : String) (log : String → IO Unit := IO.eprintln)
    (params : LeanCrypto.Password.Params := {}) : Service :=
  Service.ofRouter (Router.build! (routes repo dummy params)) (stack log)

end PrivateGames.App
