/-
  Compile-time regressions for the property commands (M9, M10). The build
  fails if an expected diagnosis changes.
-/
import Tests.Props

namespace Tests.PropsCommands

open LeanApi.Props Tests.Props PrivateGames.Model

/-- info: #check_invariant gameStore.Fresh: searched 15 worlds × 1 environments × 1 requests
  ✓ satisfiable: initial world ⟨ids [], next 0⟩
  ✓ restrictive: rules out ⟨ids [0], next 0⟩
  ✓ inductive within the bound: no counterexample to induction
-/
#guard_msgs in
#check_invariant gameStore.Fresh on gameStore.sys using { storeSpec with reorder := some fun w => [{ w with items := w.items.reverse }] }

/-- error: #check_invariant: the invariant is not decidable, so it cannot be searched. Declare it with `invariant` (which derives the instance) or provide `DecidablePred`.
  fun x => ∀ (f : Nat → Nat), f 0 = f 0 -/
#guard_msgs (error, drop info) in
#check_invariant (fun (_ : gameStore.sys.World) => ∀ f : Nat → Nat, f 0 = f 0) on gameStore.sys using storeSpec

/-- error: invariant: field `mono` is not decidable, so no runtime check can be derived from it. Add a `Decidable` instance for its statement, or mark it `proof_only` (it is then proved but left out of `Mono.check`). -/
#guard_msgs (error) in
invariant Mono (f : Nat → Nat) where
  mono : ∀ n, f n ≤ f (n + 1)

invariant MonoZ (f : Nat → Nat) where
  proof_only mono : ∀ n, f n ≤ f (n + 1)
  zero : f 0 = 0

example : MonoZ.check id = .ok () := MonoZ.check_of id ⟨fun _ => Nat.le_succ _, rfl⟩

structure Counter where
  n : Nat
  cap : Nat

invariant Counter.Ok (c : Counter) where
  bounded : c.n ≤ c.cap

def Counter.incr (c : Counter) : Except String Counter :=
  if c.n < c.cap then .ok { c with n := c.n + 1 } else .error "full"

def Counter.reset (c : Counter) : Except String Counter := .ok { c with n := 0 }

def Counter.shrink (c : Counter) : Except String Counter := .ok { c with cap := c.cap - 1 }

preserves Counter.Ok by Counter.incr, Counter.reset

example := Counter.Ok.preserved_incr

/-- error: preserves: `invariant_cases` could not close every obligation. Add a case `| f => tactic` for each function below; the goals are tagged by field and the branch conditions are named `c₁, c₂, …`.

`Tests.PropsCommands.Counter.shrink` (Tests.PropsCommands.Counter.Ok.preserved_shrink) leaves:

  case refl.bounded
  c : Counter
  hI : c.Ok
  ⊢ c.n ≤ c.cap - 1 -/
#guard_msgs (error) in
preserves Counter.Ok by Counter.shrink

end Tests.PropsCommands
