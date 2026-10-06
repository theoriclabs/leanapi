/- `require` on a proposition with no `Decidable` instance names the proposition. -/
import LeanApi.Core
open LeanApi.Core

inductive CheckError where
  | failed

def check : Op CheckError Unit := do
  let ⟨_⟩ ← require (∀ n : Nat, n + 0 = n) .failed
  pure ()
