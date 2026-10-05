import LeanApi.Core.Flow

/-! # Operations in memory

The reference runner for operations: LeanDB's in-memory backend (`LeanDb.Model.Memory`)
answers the embedded storage requests, and this module adds the operation state around its
store: the clock, the sessions started, and the KDF work done (a deterministic TEST KDF, not
a cryptographic one). A command's domain error discards every write, as a native transaction
rolls back; a storage fault aborts the run. It is a test and reference backend, not a proof
of the native runtime's behavior. -/

namespace LeanApi.Memory
open Ontology LeanDb.Model LeanApi.Core

/-- LeanDB's store, with the operation state around it. -/
structure Store where
  now : Instant
  storage : LeanDb.Model.Memory.Store := {}
  /-- Profile keys of sessions started, in order (the reference backend has no tokens). -/
  sessions : List String := []
  /-- KDF evaluations performed (hash or verify, including decision-2 dummy work). -/
  kdfRuns : Nat := 0

abbrev Fault := LeanDb.Model.Memory.Fault
abbrev Engine := StateT Store (Except Fault)

variable {resources : Resources}

/-- Run one step of LeanDB's in-memory backend on the store. -/
def onStorage (step : LeanDb.Model.Memory.Engine A) : Engine A := do
  let store ← get
  match step.run store.storage with
  | .ok (value, after) =>
    set { store with storage := after }
    pure value
  | .error fault => throw fault

/-- The row with this identity, if any (tests build actors from it). -/
def lookup [Entity T] (ref : Ref T) : Engine (Option (Row Scope T)) :=
  onStorage (LeanDb.Model.Memory.lookup ref)

/-- Rows of one entity in the store. -/
def rowCount (store : Store) (entity : String) : Nat :=
  (store.storage.rows.filter (·.1.entity.name == entity)).length

/-- TEST KDF, not cryptographic: a deterministic stand-in so the reference backend can store
and verify `PasswordHash`es. Native runtimes use their real KDF (scrypt under `KDFGate`). -/
def testKdf (password : Password) : String :=
  "memory-test-kdf$" ++ toString (hash ("leanapi-memory-salt" ++ password.value))

private def runKdf (password : Password) : Engine String := do
  modify fun store => { store with kdfRuns := store.kdfRuns + 1 }
  return testKdf password

def request : RequestF resources Scope k A → Engine A
  | .now => do return (← get).now
  | .storage req => onStorage (LeanDb.Model.Memory.request req)
  | .hashPassword password => do return Trusted.passwordHash (← runKdf password)
  | @RequestF.verifyCredential _ _ T C instT instC _credentials link profile password => do
    let _ : Entity T := instT
    let _ : Entity C := instC
    -- Decision 2: the same KDF work whether or not the profile exists.
    let candidate ← runKdf password
    match profile with
    | none => return none
    | some row =>
      let credentials ← onStorage (LeanDb.Model.Memory.entityRows (Scope := Scope) (T := C))
      let accepted := credentials.any fun credential =>
        link.profile.get credential.value == row.id &&
          Trusted.passwordHashText (link.hash.get credential.value) == candidate
      return if accepted then some row.id else none
  | @RequestF.startSession _ _ T instT _storage _authentication profile => do
    let _ : Entity T := instT
    modify fun store => { store with sessions := store.sessions ++ [profile.key] }
    return Trusted.session profile

def algebra : Algebra Engine k Scope resources := ⟨request⟩

/-- Run a read-only flow on a snapshot. -/
def read (flow : Flow .query Scope E A resources) (store : Store) : Except Fault (Except E A × Store) :=
  (flow.run algebra).run store

/-- Run a read-write flow. A domain error discards every write; a fault aborts the run. -/
def command (flow : Flow .command Scope E A resources) (store : Store) : Except Fault (Except E A × Store) := do
  let (result, after) ← (flow.run algebra).run store
  match result with | .ok _ => pure (result, after) | .error _ => pure (result, store)

end LeanApi.Memory
