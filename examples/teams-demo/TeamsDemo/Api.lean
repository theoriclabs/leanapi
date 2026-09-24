/-
  The teams demo's HTTP API. Each endpoint's type is its specification: who
  may call it, what it reads or writes, and how it can fail.
-/
import TeamsDemo.Schema
import LeanApi.Auth.Tokens

namespace TeamsDemo

open LeanApi Lean LeanDb PolicyView

/-! ## Requests and responses -/

instance : SmartCtor TeamId Nat := ⟨TeamId.make, (·.n)⟩
instance : SmartCtor UserId Nat := ⟨UserId.make, (·.n)⟩

structure SignupBody where
  email : String
  name : String
  team : TeamId

instance : FromBody SignupBody :=
  FromBody.record (SignupBody.mk <$> Fields.req "email" <*> Fields.req "name" <*> Fields.req "team")

structure UserView where
  id : Nat
  email : String
  name : String
  team : Nat
  deriving ToJson

def userView (u : Stored UserRow) : UserView :=
  ⟨(uid u.id).n, u.val.email, u.val.name, (tid u.val.team).n⟩

structure SignupView where
  user : UserView
  token : String
  deriving ToJson

/-! ## Failures -/

inductive ApiError where
  | notFound
  | unknownTeam
  | tryAgain

instance : ToProblem ApiError where
  status
    | .notFound => ⟨404, by decide⟩
    | .unknownTeam => ⟨422, by decide⟩
    | .tryAgain => ⟨503, by decide⟩
  detail
    | .notFound => none
    | .unknownTeam => some "no such team"
    | .tryAgain => some "try again"

/-! ## Who is asking -/

/-- A bearer token names a user; the actor is that user and their team. -/
def tokenMe (t : String) : Read TeamsDb (Option Me) := do
  match ← Read.lookup TokenRow TokenRow.Unique.byDigest (Tokens.digest t) with
  | none => return none
  | some tok =>
    match ← Read.get UserRow tok.val.user with
    | none => return none
    | some u => return some ⟨uid u.id, tid u.val.team⟩

instance teamsAuth : AuthenticatesDb TeamsDb Me :=
  AuthenticatesDb.sessions tokenMe (realm := "teams")

/-! ## Endpoints -/

/-- Sign up to a team. The answer carries your token. -/
def signup (body : Body SignupBody) (token : FreshToken) :
    Tx TeamsDb ApiError (Created SignupView) := do
  let row : UserRow := { email := body.val.email, name := body.val.name, team := tref body.val.team }
  match ← Txn.insert UserRow (Checked.of row trivial) with
  | .error (.duplicate ix _) => nomatch ix  -- users have no unique key: nothing can clash
  | .error (.missingRef _) => Txn.throw .unknownTeam
  | .ok user =>
    match ← Txn.insert TokenRow (Checked.of ⟨Tokens.digest token.val, user.id⟩ trivial) with
    | .error _ => Txn.throw .tryAgain
    | .ok _ =>
      let view := userView user.toStored
      pure ⟨⟨view, token.val⟩, some s!"/users/{view.id}"⟩

/-- A user on your team. Anyone else is a 404, like a missing user. -/
def getUser (me : Auth Me) (id : Path UserId) : Read TeamsDb (Except ApiError UserView) :=
  ReadAs.forAuth me fun _ => do
    match ← ReadAs.get UserRow (uref id.val) with
    | some u => return .ok (userView u.toStored)
    | none => return .error .notFound

/-- Everyone on your team. -/
def myTeam (me : Auth Me) : Read TeamsDb (List UserView) :=
  ReadAs.forAuth me fun _ => do
    return (← ReadAs.all UserRow).map (userView ·.toStored)

def teamsApi : DbApi TeamsDb := api! [
  .post "/users"          signup,
  .get  "/users/{id:nat}" getUser,
  .get  "/team"           myTeam
]

/-! ## Seed (trusted, unscoped): two teams -/

def seedTxn : {σ : Type} → Txn σ TeamsDb String Unit := do
  for name in ["Acme", "Globex"] do
    match ← Txn.insert TeamRow (Checked.of ⟨name⟩ trivial) with
    | .ok _ => pure ()
    | .error _ => Txn.throw "seed failed"

def seed (conn : Conn) : IO Unit := do
  match ← DbM.run conn (Txn.run (s := TeamsDb) (ε := String) seedTxn) with
  | .ok (.ok (.ok ())) => pure ()
  | .ok (.ok (.error e)) => throw (IO.userError e)
  | .ok (.error f) => throw (IO.userError s!"seed fault: {f}")
  | .error e => throw (IO.userError s!"seed: {e}")

end TeamsDemo
