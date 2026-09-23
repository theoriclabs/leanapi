/-
  Runtime checks from the same definition (PROPERTIES.md P7, decision 0017).

  An invariant declared with `invariant` has a generated `check`. A
  `StoredInvariant` packages that check with the proof that it agrees with
  the property, and is what storage calls on every load and before every
  write. Because the check is the generated one, the runtime check and the
  proved property cannot drift: `guardWrite_ok` and `guardLoad_ok` say that
  whatever passes the guard satisfies the `Prop`.

  LeanDB 0.4.0 has no per-entity invariant hook, so the adapter is a plain
  function the repository calls inside its transaction. If LeanDB gains one,
  `StoredInvariant.check` is the function to register.
-/
import LeanApi.Props.Authoring

namespace LeanApi.Props

structure StoredInvariant (α : Type) where
  name : String
  Holds : α → Prop
  check : α → Except (List String) Unit
  /-- The check is sound: passing it establishes the property. -/
  sound : ∀ x, check x = .ok () → Holds x

namespace StoredInvariant

variable {α : Type} (I : StoredInvariant α)

/-- The message storage reports for a failing row. -/
def describe (what : String) (fields : List String) : String :=
  s!"{what} does not satisfy {I.name} (failing: {", ".intercalate fields})"

/-- Refuse to write a value that fails the invariant. -/
def guardWrite (x : α) : Except String α :=
  match I.check x with
  | .ok () => .ok x
  | .error fs => .error (I.describe "refusing to write a value that" fs)

/-- Re-validate a loaded value. -/
def guardLoad (what : String) (x : α) : Except String α :=
  match I.check x with
  | .ok () => .ok x
  | .error fs => .error (I.describe what fs)

theorem guardWrite_ok {x y : α} (h : I.guardWrite x = .ok y) : y = x ∧ I.Holds x := by
  unfold guardWrite at h
  split at h
  · rename_i hc; cases h; exact ⟨rfl, I.sound x hc⟩
  · cases h

theorem guardLoad_ok {what : String} {x y : α} (h : I.guardLoad what x = .ok y) : y = x ∧ I.Holds x := by
  unfold guardLoad at h
  split at h
  · rename_i hc; cases h; exact ⟨rfl, I.sound x hc⟩
  · cases h

end StoredInvariant

end LeanApi.Props
