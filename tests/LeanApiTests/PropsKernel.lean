/-
  The property kernel on its own (`LeanApi.Props.Kernel`, the `LeanProps` library): no server
  import, and `preserves` over a transition that returns its next state with an output, the
  shape of a UI component's `update : Msg → Model → Model × Cmd Msg`.
-/
import LeanApi.Props.Kernel

namespace Tests.PropsKernel

open LeanApi.Props

inductive Msg where
  | add (n : Nat)
  | reset

/-- What a transition asks for afterwards (a UI component's commands). -/
inductive Out where
  | none
  | log (text : String)

/-- A counter capped at 10: adding past the cap is ignored. -/
def update : Msg → Nat → Nat × Out
  | .add n, count => if count + n ≤ 10 then (count + n, .log "added") else (count, .none)
  | .reset, _ => (0, .log "reset")

invariant Capped (count : Nat) where
  le : count ≤ 10

preserves Capped by update

/--
info: Capped.preserved_update : ∀ (a : Msg) (a_1 s' : Nat) (out : Out), Capped a_1 → update a a_1 = (s', out) → Capped s'
-/
#guard_msgs in #check @Capped.preserved_update

/-- A transition that breaks the invariant is reported, as for `Except` decisions. -/
def overflow : Msg → Nat → Nat × Out
  | _, count => (count + 1, .none)

/--
error: preserves: `invariant_cases` could not close every obligation. Add a case `| f => tactic` for each function below; the goals are tagged by field and the branch conditions are named `c₁, c₂, …`.

`Tests.PropsKernel.overflow` (Tests.PropsKernel.Capped.preserved_overflow) leaves:

  case refl.le
  a0 : Msg
  a1 : Nat
  hI : Capped a1
  ⊢ a1 + 1 ≤ 10
-/
#guard_msgs in
preserves Capped by overflow

/-- The kernel's proof principle applies to such a system directly. -/
def counterSys : Sys where
  World := Nat
  Req := Msg
  Res := Out
  Env := Unit
  step _ msg count := let (next, out) := update msg count; (out, next)
  init count := count = 0

theorem counter_capped : Invariant counterSys (fun (count : Nat) => count ≤ 10) :=
  Invariant.of_inductive {
    init := fun (count : Nat) (h : count = 0) => by omega
    step := fun _ msg (count : Nat) (h : count ≤ 10) =>
      (Capped.preserved_update msg count (update msg count).1 (update msg count).2 ⟨h⟩ rfl).le }

end Tests.PropsKernel
