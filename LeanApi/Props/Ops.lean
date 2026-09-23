/-
  The operator algebra on invariants (docs/PROPERTIES.md §6.3), each with
  its proved rule. The residual obligation when a rule does not apply
  directly is the hypothesis of the relative form.
-/
import LeanApi.Props.Sys

namespace LeanApi.Props

open Sys

variable {S : Sys}

/-! ## Conjunction -/

theorem Inductive.and {I J : S.World → Prop} (hI : Inductive S I) (hJ : Inductive S J) :
    Inductive S (fun w => I w ∧ J w) :=
  ⟨fun w h => ⟨hI.init w h, hJ.init w h⟩, fun e r w h => ⟨hI.step e r w h.1, hJ.step e r w h.2⟩⟩

/-- `J` is inductive relative to `I`: preserved from worlds satisfying both. -/
structure InductiveRel (S : Sys) (I J : S.World → Prop) : Prop where
  init : ∀ w, S.init w → J w
  step : ∀ e r w, I w → J w → J (S.step e r w).2

/-- The relative rule: `Ind(I)` and `J` inductive relative to `I` give
    `Ind(I ∧ J)`. This is how a strengthening like `Fresh` is used. -/
theorem Inductive.and_rel {I J : S.World → Prop} (hI : Inductive S I) (hJ : InductiveRel S I J) :
    Inductive S (fun w => I w ∧ J w) :=
  ⟨fun w h => ⟨hI.init w h, hJ.init w h⟩, fun e r w h => ⟨hI.step e r w h.1, hJ.step e r w h.1 h.2⟩⟩

/-- Mutual induction for a cyclic dependency: prove the conjunction jointly. -/
theorem Inductive.and_mutual {I J : S.World → Prop} (hinit : ∀ w, S.init w → I w ∧ J w)
    (hI : ∀ e r w, I w → J w → I (S.step e r w).2) (hJ : ∀ e r w, I w → J w → J (S.step e r w).2) :
    Inductive S (fun w => I w ∧ J w) :=
  ⟨hinit, fun e r w h => ⟨hI e r w h.1 h.2, hJ e r w h.1 h.2⟩⟩

/-! ## Disjunction -/

theorem Inductive.or {I J : S.World → Prop} (hI : Inductive S I) (hJ : Inductive S J)
    (hinit : ∀ w, S.init w → I w ∨ J w) : Inductive S (fun w => I w ∨ J w) :=
  ⟨hinit, fun e r w h => h.elim (fun h => .inl (hI.step e r w h)) (fun h => .inr (hJ.step e r w h))⟩

/-- Case analysis per step: each disjunct's successor lands in some disjunct.
    Two non-inductive disjuncts can make an inductive disjunction. -/
theorem Inductive.or_cases {I J : S.World → Prop} (hinit : ∀ w, S.init w → I w ∨ J w)
    (hI : ∀ e r w, I w → I (S.step e r w).2 ∨ J (S.step e r w).2)
    (hJ : ∀ e r w, J w → I (S.step e r w).2 ∨ J (S.step e r w).2) :
    Inductive S (fun w => I w ∨ J w) :=
  ⟨hinit, fun e r w h => h.elim (hI e r w) (hJ e r w)⟩

/-! ## Indexed conjunction and disjunction -/

theorem Inductive.iInter {ι : Sort _} {I : ι → S.World → Prop} (h : ∀ i, Inductive S (I i)) :
    Inductive S (fun w => ∀ i, I i w) :=
  ⟨fun w hw i => (h i).init w hw, fun e r w hw i => (h i).step e r w (hw i)⟩

/-- **The local form.** A step that only touches some indices (a frame
    condition) splits the obligation into: the touched indices are
    re-established, and every untouched index keeps its projection. -/
theorem Inductive.iInter_local {ι : Type _} {β : ι → Type _} (proj : ∀ i, S.World → β i)
    (P : ∀ i, β i → Prop) (touches : S.Env → S.Req → S.World → ι → Prop)
    (hinit : ∀ w, S.init w → ∀ i, P i (proj i w))
    (hframe : ∀ e r w i, ¬ touches e r w i → proj i (S.step e r w).2 = proj i w)
    (hlocal : ∀ e r w i, touches e r w i → (∀ j, P j (proj j w)) → P i (proj i (S.step e r w).2)) :
    Inductive S (fun w => ∀ i, P i (proj i w)) := by
  refine ⟨hinit, fun e r w hw i => ?_⟩
  by_cases ht : touches e r w i
  · exact hlocal e r w i ht hw
  · rw [hframe e r w i ht]; exact hw i

theorem Inductive.iUnion {ι : Sort _} {I : ι → S.World → Prop} (h : ∀ i, Inductive S (I i))
    (hinit : ∀ w, S.init w → ∃ i, I i w) : Inductive S (fun w => ∃ i, I i w) :=
  ⟨hinit, fun e r w ⟨i, hi⟩ => ⟨i, (h i).step e r w hi⟩⟩

/-! ## Pullback along a simulation -/

/-- `f` maps each step of `S` to a step of `T`, or to no step at all
    (stuttering: an internal step of `S` that `T` does not see). -/
structure Simulation (S T : Sys) (f : S.World → T.World) : Prop where
  init : ∀ w, S.init w → T.init (f w)
  step : ∀ e r w, f (S.step e r w).2 = f w ∨ ∃ e' r', f (S.step e r w).2 = (T.step e' r' (f w)).2

theorem Inductive.pullback {T : Sys} {f : S.World → T.World} {I : T.World → Prop}
    (hsim : Simulation S T f) (hI : Inductive T I) : Inductive S (fun w => I (f w)) := by
  refine ⟨fun w h => hI.init _ (hsim.init w h), fun e r w hw => ?_⟩
  rcases hsim.step e r w with h | ⟨e', r', h⟩
  · rw [h]; exact hw
  · rw [h]; exact hI.step e' r' _ hw

theorem Simulation.reachable {T : Sys} {f : S.World → T.World} (hsim : Simulation S T f)
    {w : S.World} (hw : Reachable S w) : Reachable T (f w) := by
  induction hw with
  | init h => exact .init (hsim.init _ h)
  | step e r _ ih =>
    rcases hsim.step e r _ with h | ⟨e', r', h⟩
    · rw [h]; exact ih
    · rw [h]; exact .step e' r' ih

/-- Invariants (not only inductive ones) transfer along a simulation. -/
theorem Invariant.pullback {T : Sys} {f : S.World → T.World} {I : T.World → Prop}
    (hsim : Simulation S T f) (hI : Invariant T I) : Invariant S (fun w => I (f w)) :=
  fun _ hw => hI _ (hsim.reachable hw)

/-! ## Union of transition sources (one obligation per writer) -/

/-- One source of transitions over a shared world: a route, a job, an admin
    command, a migration. -/
structure Writer (World Env : Type) where
  name : String
  Req : Type
  Res : Type
  step : Env → Req → World → Res × World

/-- The system whose steps are those of any listed writer. -/
def Sys.ofWriters {World Env : Type} (ws : List (Writer World Env)) (init : World → Prop) : Sys where
  World := World
  Req := Σ i : Fin ws.length, (ws.get i).Req
  Res := Σ i : Fin ws.length, (ws.get i).Res
  Env := Env
  step e r w := let (res, w') := (ws.get r.1).step e r.2 w; (⟨r.1, res⟩, w')
  init := init

/-- A writer preserves `I`. -/
def Writer.Preserves {World Env : Type} (wr : Writer World Env) (I : World → Prop) : Prop :=
  ∀ e r w, I w → I (wr.step e r w).2

/-- **Union rule.** An invariant of a union of writers needs exactly one
    obligation per writer. Adding a writer adds an obligation. -/
theorem Inductive.ofWriters {World Env : Type} {ws : List (Writer World Env)} {init : World → Prop}
    {I : World → Prop} (hinit : ∀ w, init w → I w) (hws : ∀ wr ∈ ws, wr.Preserves I) :
    Inductive (Sys.ofWriters ws init) I := by
  refine ⟨hinit, fun e r w hw => ?_⟩
  exact hws _ (List.get_mem ws r.1) e r.2 w hw

/-- And conversely: if the union is inductive for every initial world
    predicate, each writer preserves `I` (the obligations are necessary). -/
theorem Inductive.ofWriters_iff {World Env : Type} {ws : List (Writer World Env)} {I : World → Prop} :
    Inductive (Sys.ofWriters ws I) I ↔ ∀ wr ∈ ws, wr.Preserves I := by
  constructor
  · intro h wr hmem e r w hw
    obtain ⟨i, rfl⟩ := List.get_of_mem hmem
    exact h.step e ⟨i, r⟩ w hw
  · exact fun h => Inductive.ofWriters (fun _ h => h) h

end LeanApi.Props
