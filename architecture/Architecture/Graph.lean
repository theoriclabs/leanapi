/-
  The shape of a codebase, as something a proof can talk about.

  * A `Graph` is a list of edges.
  * `imports% R₁ R₂ …` is this build's import graph: an edge `(m, i)` for
    every module `m` named `Rₖ` or `Rₖ.…`, and every module `i` that `m`
    imports. The elaborator reads it from the environment: it is the graph
    Lean compiled, not a description of it. (The elaborator is trusted, like
    any Lean meta program.)
  * A design is a graph over a few named parts. A codebase conforms to a
    design, through a map from modules to parts, when every import follows a
    path of the design (`Conforms`). Then every chain of imports does
    (`Conforms.reaches`). So a rule such as "the proof library never reaches
    the server" is proved from a check of each import and a fact about the
    small design graph (`not_reaches_of_check`).
-/
import Lean

namespace Architecture

/-- A directed graph, as its list of edges. -/
structure Graph (V : Type) where
  edges : List (V × V)

namespace Graph

variable {V W : Type}

/-- `a` reaches `b` by following zero or more edges. -/
inductive Reaches (g : Graph V) : V → V → Prop
  | refl (a : V) : Reaches g a a
  | step {a b c : V} : (a, b) ∈ g.edges → Reaches g b c → Reaches g a c

theorem Reaches.trans {g : Graph V} {a b c : V} (h₁ : g.Reaches a b) (h₂ : g.Reaches b c) :
    g.Reaches a c := by
  induction h₁ with
  | refl => exact h₂
  | step e _ ih => exact .step e (ih h₂)

/-! ## Deciding reachability -/

/-- Whether `a` reaches `b` in at most `n` edges, computed. -/
def reach [DecidableEq V] (g : Graph V) : Nat → V → V → Bool
  | 0, a, b => decide (a = b)
  | n + 1, a, b => decide (a = b) || g.edges.any fun e => decide (e.1 = a) && g.reach n e.2 b

theorem reach_sound [DecidableEq V] {g : Graph V} :
    ∀ {n : Nat} {a b : V}, g.reach n a b = true → g.Reaches a b
  | 0, a, b, h => by
    simp only [reach, decide_eq_true_eq] at h
    subst h; exact .refl a
  | n + 1, a, b, h => by
    simp only [reach, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at h
    rcases h with rfl | ⟨⟨x, y⟩, hmem, hx, hr⟩
    · exact .refl _
    · simp only at hx hr; subst hx
      exact .step hmem (reach_sound hr)

theorem reach_self [DecidableEq V] (g : Graph V) (n : Nat) (a : V) : g.reach n a a = true := by
  cases n <;> simp [reach]

/-- A path never needs more steps than there are edges. -/
def fuel (g : Graph V) : Nat := g.edges.length

/-- A set closed under edges: whatever it holds, it holds every successor of. -/
def Closed (g : Graph V) (S : V → Prop) : Prop := ∀ e ∈ g.edges, S e.1 → S e.2

theorem Reaches.closed {g : Graph V} {S : V → Prop} (hc : g.Closed S) {a b : V}
    (hr : g.Reaches a b) (ha : S a) : S b := by
  induction hr with
  | refl => exact ha
  | step e _ ih => exact ih (hc _ e ha)

/-- `a` does not reach `b`, by computing what `a` reaches: that set is
    closed under edges and leaves out `b`. Prove the premise with `decide`. -/
theorem not_reaches_of_check [DecidableEq V] {g : Graph V} {a b : V}
    (h : ((g.edges.all fun e => !g.reach g.fuel a e.1 || g.reach g.fuel a e.2) &&
      !g.reach g.fuel a b) = true) : ¬ g.Reaches a b := by
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at h
  intro hr
  have hc : g.Closed fun x => g.reach g.fuel a x = true := fun e he ha => by
    rcases h.1 e he with h' | h'
    · simp only [h'] at ha; cases ha
    · exact h'
  have := hr.closed hc (reach_self g _ a)
  rw [h.2] at this; cases this

/-! ## Conforming to a design -/

/-- Every edge of `g` joins two classified vertices, and follows a path of
    the design `d`. -/
def Conforms (g : Graph V) (d : Graph W) (part : V → Option W) : Prop :=
  ∀ e ∈ g.edges, ∃ p q, part e.1 = some p ∧ part e.2 = some q ∧ d.Reaches p q

/-- Conformance lifts from single imports to chains of imports. -/
theorem Conforms.reaches {g : Graph V} {d : Graph W} {part : V → Option W}
    (h : g.Conforms d part) {a b : V} (hr : g.Reaches a b) {p q : W}
    (hp : part a = some p) (hq : part b = some q) : d.Reaches p q := by
  induction hr generalizing p with
  | refl => rw [hp] at hq; cases hq; exact .refl _
  | step e _ ih =>
    obtain ⟨p', q', h₁, h₂, hd⟩ := h _ e
    rw [hp] at h₁; cases h₁
    exact hd.trans (ih h₂ hq)

/-- The edge's verdict: both ends classified, and the design allows it. -/
def allows [DecidableEq W] (d : Graph W) (part : V → Option W) (e : V × V) : Bool :=
  match part e.1, part e.2 with
  | some p, some q => d.reach d.fuel p q
  | _, _ => false

theorem conforms_of_check [DecidableEq W] {g : Graph V} {d : Graph W} {part : V → Option W}
    (h : g.edges.all (allows d part) = true) : g.Conforms d part := by
  intro e he
  have := List.all_eq_true.mp h e he
  unfold allows at this
  split at this
  · next p q h₁ h₂ => exact ⟨p, q, h₁, h₂, reach_sound this⟩
  · cases this

/-- The edges the design does not allow, one per line, for error messages. -/
def report [DecidableEq W] [ToString V] [Repr W] (g : Graph V) (d : Graph W)
    (part : V → Option W) : String :=
  let show_ (v : V) : String := match part v with
    | some p => s!"{v} ({((reprStr p).splitOn ".").getLast!})"
    | none => s!"{v} (in no part)"
  "\n".intercalate <| (g.edges.filter (!allows d part ·)).map fun e =>
    s!"  {show_ e.1} imports {show_ e.2}"

end Graph

/-! ## Reading the build's import graph -/

open Lean Elab Term in
/-- `imports% R₁ R₂ …`: the import graph of the modules under the roots
    `Rₖ` (the module `Rₖ` and every `Rₖ.…`), among the modules this file
    imports. One edge `(m, i)` per module `m` under a root and module `i`
    that `m` imports directly. -/
elab "imports% " roots:ident+ : term => do
  let env ← getEnv
  let names := env.header.moduleNames
  for r in roots do
    unless names.any (r.getId.isPrefixOf ·) do
      throwErrorAt r "imports%: no module under `{r.getId}` is imported by this file"
  let under (m : Name) : Bool := roots.any (·.getId.isPrefixOf m)
  let mut edges : Array (Name × Name) := #[]
  for m in names, d in env.header.moduleData do
    if under m then
      for i in d.imports do
        unless edges.contains (m, i.module) do
          edges := edges.push (m, i.module)
  return mkApp2 (mkConst ``Graph.mk) (mkConst ``Name) (toExpr edges.toList)

open Lean Elab Tactic Meta in
/-- Prove `Graph.Conforms g d part` by computation, checked by the kernel.
    When an import breaks the design, the error names it. -/
elab "conforms" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let (``Graph.Conforms, #[_, _, g, d, part]) := ty.getAppFnArgs
    | throwError "conforms: the goal is not `Graph.Conforms g d part`"
  let msg ← unsafe evalExpr String (mkConst ``String) (← mkAppM ``Graph.report #[g, d, part])
  unless msg.isEmpty do
    throwError "these imports do not follow the design:\n{msg}"
  evalTactic (← `(tactic| exact Graph.conforms_of_check (by decide +kernel)))

end Architecture
