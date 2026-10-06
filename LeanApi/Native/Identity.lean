import LeanOntology
import LeanDb

namespace LeanApi.Native
open Ontology

/-- Check the portable parser and application scope before crossing into native IDs.
This is a trusted schema-bound mapping, never an implicit Nat/Int coercion. -/
def nativeRef [HasTypeId T] [LeanDb.Entity T] (ref : Ontology.Ref T)
    (scope : String := "default") : Validation (LeanDb.Id T) := do
  if ref.scope.value != scope then Validation.fail "identity.scope_mismatch" [.key "scope"]
  let checked ← Ontology.Ref.parse (T := T) ref.key scope
  match checked.key.toInt? with
  | none => Validation.fail "identity.invalid_key" [.key "key"]
  | some value => pure ⟨Int64.ofInt value⟩

/-- Native IDs are accepted only when the same portable parser can reconstruct them. -/
def publicRef [HasTypeId T] [LeanDb.Entity T] (id : LeanDb.Id T)
    (scope : String := "default") : Validation (Ontology.Ref T) :=
  Ontology.Ref.parse (toString id.toInt64.toInt) scope

end LeanApi.Native
