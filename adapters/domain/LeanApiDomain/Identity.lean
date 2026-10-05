import LeanApp.Domain.Scalars
import LeanDb

namespace LeanApi.Domain
open Ontology

/-- Check the portable parser and application scope before crossing into native IDs.
This is a trusted schema-bound mapping, never an implicit Nat/Int coercion. -/
def nativeRef [HasTypeId T] [LeanDb.Entity T] (ref : LeanApp.Domain.Ref T)
    (scope : String := "default") : Validation (LeanDb.Id T) := do
  if ref.scope.value != scope then Validation.fail "identity.scope_mismatch" [.key "scope"]
  let checked ← LeanApp.Domain.Ref.parse (T := T) ref.key scope
  match checked.key.toInt? with
  | none => Validation.fail "identity.invalid_key" [.key "key"]
  | some value => pure ⟨Int64.ofInt value⟩

/-- Native IDs are accepted only when the same portable parser can reconstruct them. -/
def publicRef [HasTypeId T] [LeanDb.Entity T] (id : LeanDb.Id T)
    (scope : String := "default") : Validation (LeanApp.Domain.Ref T) :=
  LeanApp.Domain.Ref.parse (toString id.toInt64.toInt) scope

end LeanApi.Domain
