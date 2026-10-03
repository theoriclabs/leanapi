import LeanApiDomain.Identity
import LeanApiDomain.Contract
import LeanDbDomain.Access
import LeanDb.Typed.Constraint
import LeanDbDomain.Operations

namespace LeanApi.Domain.Native
open LeanDb LeanApp.Domain

abbrev CommandM (Scope s Error : Type) [IsSchema s] := Txn Scope s (Contract.CallError Error)

def fault (code : String) (status : Nat := 500) : Contract.CallError Error :=
  .protocol ⟨code, some status, ""⟩

/-- Only the exact generated declaration can discharge a native constraint.
Conflict holders, restricting counts and database rows never enter the reply. -/
def constraintFailure (constraints : List (LeanApp.Domain.Constraint Error))
    (identity : String) : Contract.CallError Error :=
  match constraints.find? (fun constraint => constraint.identity == identity) with
  | some constraint => .domain constraint.publicFailure
  | none => fault "storage.unmapped_constraint"

def create {s Scope T Error : Type} [IsSchema s] [LeanApp.Domain.Entity T]
    (storage : LeanDb.Domain.EntityStorage s T) (value : T)
    (constraints : List (LeanApp.Domain.Constraint Error)) : CommandM Scope s Error (LeanApp.Domain.Ref T) :=
  letI := storage.entity
  letI := storage.indexes
  letI := storage.unique
  letI := storage.foreignKey
  letI := storage.schema
  do
    let checked ← (LeanDb.Entity.check T value).orAbort (fun _ => fault "storage.invalid_row" 422)
    let row ← (Txn.insert T checked).orAbort fun
      | .duplicate index _ => constraintFailure constraints (storage.sourceUnique index)
      | .missingRef key => constraintFailure constraints (ForeignKey.metadata key).identity
    (publicRef row.id).orAbort (fun _ => fault "storage.invalid_identity")

/-- Re-read in the admitted transaction and write exactly the generated patch's
columns. No full-row UPDATE and no member-table rewrite. -/
def change {s Scope T Error : Type} [IsSchema s] [LeanApp.Domain.Entity T]
    (storage : LeanDb.Domain.EntityStorage s T) (row : LeanApp.Domain.Row Scope T)
    (patch : LeanApp.Domain.Change T) (constraints : List (LeanApp.Domain.Constraint Error)) :
    CommandM Scope s Error Unit :=
  letI := storage.entity
  letI := storage.indexes
  letI := storage.unique
  letI := storage.foreignKey
  letI := storage.schema
  do
    let id ← (nativeRef row.id).orAbort (fun _ => fault "identity.invalid_reference" 400)
    let some live ← Txn.get T id | Txn.throw (fault "storage.gone" 409)
    if !(patch.fields.all fun name => (LeanDb.Entity.fields (α := T)).any fun f =>
        LeanDb.Entity.fieldName f == name) then
      Txn.throw (fault "storage.invalid_patch" 422)
    let fields : LeanDb.Fields T := ⟨fun f => patch.fields.contains (LeanDb.Entity.fieldName f)⟩
    let checked ← (LeanDb.Entity.check T (patch.apply live.val)).orAbort
      (fun _ => fault "storage.invalid_row" 422)
    discard <| (Txn.patch T live fields checked).orAbort fun
      | .duplicate index _ => constraintFailure constraints (storage.sourceUnique index.ix)
      | .missingRef key => constraintFailure constraints (ForeignKey.metadata key.fk).identity
      | .gone => fault "storage.gone" 409
      | .invalid _ => fault "storage.invalid_patch" 422

def remove {s Scope T Error : Type} [IsSchema s] [LeanApp.Domain.Entity T]
    (storage : LeanDb.Domain.EntityStorage s T) (row : LeanApp.Domain.Row Scope T)
    (constraints : List (LeanApp.Domain.Constraint Error)) : CommandM Scope s Error Unit :=
  letI := storage.entity
  letI := storage.schema
  letI := storage.referencedBy
  do
    let id ← (nativeRef row.id).orAbort (fun _ => fault "identity.invalid_reference" 400)
    discard <| (Txn.delete T id).orAbort fun
      | .gone => fault "storage.gone" 409
      | .restricted key _ => constraintFailure constraints (ReferencedBy.metadata key.val).identity

/-- LeanDB's plain storage-step failures (`LeanDb.Domain.StorageFault`) as typed framework
replies. None of them is a domain conflict: declared conflicts come back as values. -/
def storageFault (fault : LeanDb.Domain.StorageFault) : Contract.CallError Error :=
  Native.fault fault.code (match fault with
    | .invalidReference _ => 400
    | .invalidRow _ => 422
    | .missingReference _ | .restricted _ | .gone => 409
    | .invalidIdentity _ | .unmappedConflict _ => 500)

def includeActor {s Scope Parent Target Error : Type} [IsSchema s]
    (storage : LeanDb.Domain.MemberStorage s Parent Target)
    (parent : LeanApp.Domain.Ref Parent) (actor : SignedIn Scope Target)
    (constraints : List (LeanApp.Domain.Constraint Error)) : CommandM Scope s Error Unit :=
  letI := storage.edge.entity
  letI := storage.edge.foreignKey
  do
    match storage.includeActor parent actor (fault "storage.gone" 409) with
    | .error _ => Txn.throw (fault "identity.invalid_membership" 400)
    | .ok program => discard <| program.orAbort (fun key =>
        constraintFailure constraints (ForeignKey.metadata key).identity)

end LeanApi.Domain.Native
