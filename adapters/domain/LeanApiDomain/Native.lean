import LeanApiDomain.NativeResources
import LeanApiDomain.Execution
import LeanApiDomain.Prepared

namespace LeanApi.Domain.Native
open LeanApi LeanDb LeanApp.Domain

private def checkedRead {s E A} [IsSchema s] (program : Except String (Read s A)) :
    ExceptT (Contract.CallError E) (Read s) A :=
  match program with
  | .error _ => throw (fault "identity.invalid_reference" 400)
  | .ok program => liftM program

def contains {s Scope E P T} [IsSchema s]
    (relation : MemberHandle Scope P T (resources s)) (member : LeanApp.Domain.Ref T) :
    ExceptT (Contract.CallError E) (Read s) Bool :=
  checkedRead (relation.storage.contains relation.parent member)

def readRequest {s Scope E A} [IsSchema s] (env : Env) :
    Request Scope E .query A (resources s) → ExceptT (Contract.CallError E) (Read s) A
  | .now => match Instant.ofEpochSeconds (Int.ofNat env.now) with
    | .ok now => pure now
    | .error _ => throw (fault "clock.invalid")
  | @RequestF.find _ _ _ _ _ _ storage reference => checkedRead (storage.find reference)
  -- DDD-LR-05 plain requests, through LeanDB's storage-step hooks (`LeanDbDomain.Operations`).
  | @RequestF.select _ _ _ _ _ instanceT storage => do
    letI := instanceT
    match ← liftM storage.select with
    | .ok rows => pure rows
    | .error error => throw (storageFault error)
  | @RequestF.findBy _ _ _ _ _ _ instanceT storage _ lookup key => do
    letI := instanceT
    match ← liftM (storage.findBy lookup key) with
    | .ok row => pure row
    | .error error => throw (storageFault error)
  -- A join (`Query.linkField`): one column of each linked target, by target id (LeanDB's
  -- `LinkEvidence.project`).
  | @RequestF.linkField _ _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent =>
    match link.project targets column parent with
    | .error _ => throw (fault "identity.invalid_reference" 400)
    | .ok program => liftM program

/-- The stored hash of a profile's authored credential, read through `link` (no unique on the
credential's profile field is assumed, so this is the credential table's id-ordered scan). -/
def storedHash {s T C E} [IsSchema s] [LeanApp.Domain.Entity C]
    (credentials : LeanDb.Domain.EntityStorage s C) (link : CredentialLink C T) (profile : LeanApp.Domain.Ref T) :
    Read s (Except (Contract.CallError E) (Option String)) := do
  match ← credentials.select (Scope := Unit) with
  | .error error => return .error (storageFault error)
  | .ok rows =>
    return .ok ((rows.find? fun row => link.profile.get row.value == profile).map fun row =>
      LeanApp.Domain.Trusted.passwordHashText (link.hash.get row.value))

def commandRequest {s Scope E A} [IsSchema s] (env : Env)
    (admission : Option Auth.Admission) (ttl : Nat) (preparation : Option Auth.Preparation := none) :
    Request Scope E .command A (resources s) → CommandM Scope s E A
  | .now => (Instant.ofEpochSeconds (Int.ofNat env.now)).orAbort (fun _ => fault "clock.invalid")
  | @RequestF.find _ _ _ _ _ _ storage reference =>
    match storage.find reference with
    | .error _ => Txn.throw (fault "identity.invalid_reference" 400)
    | .ok program => Txn.ofRead program
  | @RequestF.create _ _ _ T instanceT storage value constraints =>
    letI := instanceT
    create storage value constraints
  | @RequestF.change _ _ _ T instanceT storage row patch constraints =>
    letI := instanceT
    change storage row patch constraints
  | @RequestF.remove _ _ _ T instanceT storage row constraints =>
    letI := instanceT
    remove storage row constraints
  | .include relation actor constraints => includeActor relation.storage relation.parent actor constraints
  | @RequestF.signUp _ _ _ T instanceT _ store value _ password constraints =>
    letI := instanceT
    match admission with
    | none => Txn.throw (fault "auth.preparation_required")
    | some prepared => store.signUp env prepared value password constraints ttl
  | @RequestF.signIn _ _ _ _ _ _ store _ address password invalidCredentials =>
    match admission with
    | none => Txn.throw (fault "auth.preparation_required")
    | some prepared => store.signIn env prepared address password invalidCredentials ttl
  -- DDD-LR-05 plain requests, through LeanDB's storage-step hooks: a declared unique
  -- conflict is a value; every StorageFault is a framework abort of this transaction.
  | @RequestF.insert _ _ _ _ _ instanceT storage value conflicts =>
    letI := instanceT
    storage.insert value conflicts storageFault
  | @RequestF.update _ _ _ _ _ instanceT storage row patch conflicts =>
    letI := instanceT
    storage.update row patch conflicts storageFault
  | @RequestF.delete _ _ _ _ instanceT storage row =>
    letI := instanceT
    storage.delete row storageFault
  | @RequestF.findBy _ _ _ _ _ _ instanceT storage _ lookup key => do
    letI := instanceT
    match ← Txn.ofRead (storage.findBy lookup key) with
    | .ok row => pure row
    | .error error => Txn.throw (storageFault error)
  | @RequestF.select _ _ _ _ _ instanceT storage => do
    letI := instanceT
    match ← Txn.ofRead storage.select with
    | .ok rows => pure rows
    | .error error => Txn.throw (storageFault error)
  | @RequestF.linkField _ _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent =>
    match link.project targets column parent with
    | .error _ => Txn.throw (fault "identity.invalid_reference" 400)
    | .ok program => Txn.ofRead program
  -- Authored authentication (design D): answered from the preparation made before admission.
  | .hashPassword password =>
    match preparation.bind (·.hashOf password) with
    | some hash => pure (LeanApp.Domain.Trusted.passwordHash hash)
    | none => Txn.throw (fault "auth.preparation_required")
  | @RequestF.verifyCredential _ _ _ T C _ instanceC credentials link subject password =>
    letI := instanceC
    match preparation, subject with
    | none, _ => Txn.throw (fault "auth.preparation_required")
    | some _, none => pure none
    | some prepared, some row => do
      match ← Txn.ofRead (storedHash credentials link row.id) with
      | .error error => Txn.throw error
      | .ok stored => pure (if prepared.verdict row.id.key password stored then some row.id else none)
  | @RequestF.startSession _ _ _ _ _ _ store subject =>
    match preparation with
    | none => Txn.throw (fault "auth.preparation_required")
    | some prepared => do
      store.startSession env prepared.session subject ttl
      pure (LeanApp.Domain.Trusted.session subject)

/-- A total DB-backed column plan. Only Flow.run's policy-first disclose branch
calls this; denied plans do not prepare or execute the protected SQL. -/
def project {s Scope E A} [IsSchema s] :
    Projection Scope A (resources s) → ExceptT (Contract.CallError E) (Read s) A
  | @ProjectionF.members _ _ _ _ _ _ relation _ selection => checkedRead (selection.project relation.parent)
  | .map plan map => do return map (← project plan)

def queryAlgebra {s Scope E} [IsSchema s] (env : Env) :
    Algebra (ExceptT (Contract.CallError E) (Read s)) .query Scope E (resources s) := {
  request := fun request => do return .ok (← readRequest env request)
  contains := contains
  project := project
}

def commandAlgebra {s Scope E} [IsSchema s] (env : Env)
    (admission : Option Auth.Admission := none) (ttl : Nat := 86400)
    (preparation : Option Auth.Preparation := none) :
    Algebra (CommandM Scope s E) .command Scope E (resources s) := {
  request := fun request => do return .ok (← commandRequest env admission ttl preparation request)
  contains := fun relation member => do
    (Txn.ofRead (contains (E := E) relation member).run).orAbort id
  project := fun plan => do (Txn.ofRead (project (E := E) plan).run).orAbort id
}

/-- Actor dictionaries are native assembly capabilities, not a second auth IR. -/
class ActorContext (Actor : Type → Type) (Profile : Type) [LeanApp.Domain.Entity Profile] : Type 1 where
  resolve : {s Scope E : Type} → [IsSchema s] →
    {profile : LeanDb.Domain.EntityStorage s Profile} → Auth.Storage s Profile profile →
    Auth.CookieConfig → Env → Req → Bool → Read s (Contract.CallResult (Actor Scope) E)

instance [LeanApp.Domain.Entity Profile] : ActorContext (fun scope => SignedIn scope Profile) Profile where
  resolve := fun store config env req mutation => do
    match ← Auth.resolve config env req store.live mutation with
    | .error error => return .error (error.mapDomain Empty.elim)
    | .ok none => return .error .unauthenticated
    | .ok (some profile) => return .ok (Trusted.signedIn profile)

instance [LeanApp.Domain.Entity Profile] : ActorContext (fun scope => Viewer scope Profile) Profile where
  resolve := fun store config env req mutation => do
    return (← Auth.resolve config env req store.live mutation).mapError
      (Contract.CallError.mapDomain Empty.elim) |>.map Trusted.viewer

/-- An `Option SignedIn` actor: `none` only when no credential is presented; a
presented but invalid credential is still 401, as for `Viewer`. -/
instance [LeanApp.Domain.Entity Profile] : ActorContext (fun scope => Option (SignedIn scope Profile)) Profile where
  resolve := fun store config env req mutation => do
    return (← Auth.resolve config env req store.live mutation).mapError
      (Contract.CallError.mapDomain Empty.elim) |>.map (·.map Trusted.signedIn)

/-- Anonymous commands keep the exact browser Origin check unless they present a bearer
token, or carry no session cookie and ask for token mode (decision 9: no cookie is set
then, so a cross-site page can plant nothing). A presented credential is still
validated. Anonymous reads need no Origin. -/
instance [LeanApp.Domain.Entity Profile] : ActorContext (fun _ => Unit) Profile where
  resolve := fun store config env req mutation => do
    match ← Auth.resolve (Scope := Unit) config env req store.live mutation with
    | .error error => return .error (error.mapDomain Empty.elim)
    | .ok _ =>
      if !mutation then return .ok ()
      return (Auth.anonymousGuard config req (Auth.tokenRequested req)).mapError
        (Contract.CallError.mapDomain Empty.elim)

end LeanApi.Domain.Native
