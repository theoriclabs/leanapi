import LeanApi.Native.NativeResources
import LeanApi.Native.NativeStorage
import LeanApi.Native.Execution
import LeanApi.Native.Prepared

/-! # The native algebra

How an operation's requests run on SQLite, at the native family `resources s`: the embedded
storage requests go to LeanDB's own interpreter (`LeanDb.Native.queryRequest` /
`commandRequest`); the clock reads the request's sampled time; the KDF requests are answered
from the preparation made before writer admission (design D); `startSession` inserts the
prepared session row in the operation's own transaction. -/
namespace LeanApi.Native
open LeanApi LeanDb LeanDb.Model LeanApi.Core

private def clockNow (env : Env) : Except Unit Instant :=
  match Instant.ofEpochSeconds (Int.ofNat env.now) with
  | .ok now => .ok now
  | .error _ => .error ()

def readRequest {s Scope E A} [IsSchema s] (env : Env) :
    Request Scope .query A (resources s) → ExceptT (Contract.CallError E) (Read s) A
  | .now => match clockNow env with
    | .ok now => pure now
    | .error _ => throw (fault "clock.invalid")
  | .storage req => do
    match ← (LeanDb.Native.queryRequest (s := s) (Scope := Scope) req).run with
    | .ok value => pure value
    | .error why => throw (storageFault why)

/-- The stored hash of a profile's authored credential, read through `link` (no unique on the
credential's profile field is assumed, so this is the credential table's id-ordered scan). -/
def storedHash {s T C E} [IsSchema s] [LeanDb.Model.Entity C]
    (credentials : LeanDb.Native.EntityStorage s C) (link : CredentialLink C T) (profile : Ontology.Ref T) :
    Read s (Except (Contract.CallError E) (Option String)) := do
  match ← credentials.select (Scope := Unit) with
  | .error error => return .error (storageFault error)
  | .ok rows =>
    return .ok ((rows.find? fun row => link.profile.get row.value == profile).map fun row =>
      Ontology.Trusted.passwordHashText (link.hash.get row.value))

def commandRequest {s Scope E A} [IsSchema s] (env : Env) (ttl : Nat)
    (preparation : Option Auth.Preparation := none) :
    Request Scope .command A (resources s) → CommandM Scope s E A
  | .now => (clockNow env).orAbort (fun _ => fault "clock.invalid")
  | .storage req => LeanDb.Native.commandRequest (s := s) (σ := Scope) storageFault req
  -- Authored authentication (design D): answered from the preparation made before admission.
  | .hashPassword password =>
    match preparation.bind (·.hashOf password) with
    | some hash => pure (Ontology.Trusted.passwordHash hash)
    | none => Txn.throw (fault "auth.preparation_required")
  | @RequestF.verifyCredential _ _ T C _ instanceC credentials link subject password =>
    letI := instanceC
    match preparation, subject with
    | none, _ => Txn.throw (fault "auth.preparation_required")
    | some _, none => pure none
    | some prepared, some row => do
      match ← Txn.ofRead (storedHash credentials link row.id) with
      | .error error => Txn.throw error
      | .ok stored => pure (if prepared.verdict row.id.key password stored then some row.id else none)
  | @RequestF.startSession _ _ _ _ _ store subject =>
    match preparation with
    | none => Txn.throw (fault "auth.preparation_required")
    | some prepared => do
      store.startSession env prepared.session subject ttl
      pure (Ontology.Trusted.session subject)

def queryAlgebra {s Scope E} [IsSchema s] (env : Env) :
    Algebra (ExceptT (Contract.CallError E) (Read s)) .query Scope (resources s) :=
  ⟨readRequest env⟩

def commandAlgebra {s Scope E} [IsSchema s] (env : Env) (ttl : Nat := 86400)
    (preparation : Option Auth.Preparation := none) :
    Algebra (CommandM Scope s E) .command Scope (resources s) :=
  ⟨commandRequest env ttl preparation⟩

/-- Actor dictionaries are native assembly capabilities, not a second auth IR. -/
class ActorContext (Actor : Type → Type) (Profile : Type) [LeanDb.Model.Entity Profile] : Type 1 where
  resolve : {s Scope E : Type} → [IsSchema s] →
    {profile : LeanDb.Native.EntityStorage s Profile} → Auth.Storage s Profile profile →
    Auth.CookieConfig → Env → Req → Bool → Read s (Contract.CallResult (Actor Scope) E)

/-- Anonymous commands of an app with accounts keep the exact browser Origin check unless they
present a bearer token, or carry no session cookie and ask for token mode (decision 9: no
cookie is set then, so a cross-site page can plant nothing). A presented credential is still
validated. Anonymous reads need no Origin. -/
instance [LeanDb.Model.Entity Profile] : ActorContext (fun _ => Unit) Profile where
  resolve := fun store config env req mutation => do
    match ← Auth.resolve (Scope := Unit) config env req store.live mutation with
    | .error error => return .error (error.mapDomain Empty.elim)
    | .ok _ =>
      if !mutation then return .ok ()
      return (Auth.anonymousGuard config req (Auth.tokenRequested req)).mapError
        (Contract.CallError.mapDomain Empty.elim)

end LeanApi.Native
