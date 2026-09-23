/-
  The property kernel (PLAN.md M8, docs/PROPERTIES.md §2 and §6).

  One small signature, `Sys`, that every library property is stated
  against, plus the theory of state invariants proved once:

  * `Reachable`, `Invariant`, `Inductive`, `Invariant.of_inductive`;
  * `Inductive.restrict`: an inductive invariant is a subsystem (§6.2);
  * `pre`, `WeakestInductive`, `invariant_iff`, and `CTI` (§6.5): when an
    invariant is not inductive, the canonical diagnosis.

  The operator algebra (§6.3) is in `LeanApi/Props/Ops.lean`.

  Nothing here is automated. Every theorem is a plain statement a user could
  apply by hand; the authoring commands (M9) only generate such statements.
-/
namespace LeanApi.Props

/-- A transition system: the signature every property is stated against.
    `Env` carries what a step may depend on besides the request (time,
    randomness, configuration). Apps with no environment use `Unit`. -/
structure Sys where
  World : Type
  Req : Type
  Res : Type
  Env : Type
  step : Env → Req → World → Res × World
  /-- Admissible initial worlds. -/
  init : World → Prop

namespace Sys

variable {S : Sys}

/-- Worlds reachable from an initial world by any sequence of steps. -/
inductive Reachable (S : Sys) : S.World → Prop where
  | init {w} : S.init w → Reachable S w
  | step {w} (e : S.Env) (r : S.Req) : Reachable S w → Reachable S (S.step e r w).2

/-- `w'` is reachable from `w` (reflexive-transitive closure of `step`). -/
inductive ReachFrom (S : Sys) : S.World → S.World → Prop where
  | refl (w) : ReachFrom S w w
  | step {w w'} (e : S.Env) (r : S.Req) : ReachFrom S w w' → ReachFrom S w (S.step e r w').2

theorem ReachFrom.trans {w₁ w₂ w₃ : S.World} (h₁ : ReachFrom S w₁ w₂) (h₂ : ReachFrom S w₂ w₃) :
    ReachFrom S w₁ w₃ := by
  induction h₂ with
  | refl => exact h₁
  | step e r _ ih => exact .step e r ih

theorem ReachFrom.first {w w' : S.World} (e : S.Env) (r : S.Req) (h : ReachFrom S (S.step e r w).2 w') :
    ReachFrom S w w' := ReachFrom.trans (.step e r (.refl w)) h

theorem Reachable.of_reachFrom {w w' : S.World} (h₀ : Reachable S w) (h : ReachFrom S w w') :
    Reachable S w' := by
  induction h with
  | refl => exact h₀
  | step e r _ ih => exact .step e r ih

theorem Reachable.iff_reachFrom {w : S.World} : Reachable S w ↔ ∃ w₀, S.init w₀ ∧ ReachFrom S w₀ w := by
  constructor
  · intro h
    induction h with
    | init hi => exact ⟨_, hi, .refl _⟩
    | step e r _ ih =>
      obtain ⟨w₀, hi, hr⟩ := ih
      exact ⟨w₀, hi, .step e r hr⟩
  · rintro ⟨w₀, hi, hr⟩
    exact Reachable.of_reachFrom (.init hi) hr

end Sys

open Sys

/-- `I` holds in every reachable world. -/
def Invariant (S : Sys) (I : S.World → Prop) : Prop := ∀ w, Reachable S w → I w

/-- `I` holds initially and is preserved by every step from any world
    satisfying it (reachable or not). The proof principle for `Invariant`. -/
structure Inductive (S : Sys) (I : S.World → Prop) : Prop where
  init : ∀ w, S.init w → I w
  step : ∀ e r w, I w → I (S.step e r w).2

theorem Invariant.of_inductive {S : Sys} {I : S.World → Prop} (h : Inductive S I) : Invariant S I := by
  intro w hw
  induction hw with
  | init hi => exact h.init _ hi
  | step e r _ ih => exact h.step e r _ ih

theorem Invariant.mono {S : Sys} {I J : S.World → Prop} (h : Invariant S I) (hIJ : ∀ w, I w → J w) :
    Invariant S J := fun w hw => hIJ w (h w hw)

theorem Invariant.and {S : Sys} {I J : S.World → Prop} (hI : Invariant S I) (hJ : Invariant S J) :
    Invariant S (fun w => I w ∧ J w) := fun w hw => ⟨hI w hw, hJ w hw⟩

/-- `Reachable` itself is the strongest invariant, and it is inductive. -/
theorem Inductive.reachable (S : Sys) : Inductive S (Reachable S) :=
  ⟨fun _ h => .init h, fun e r _ h => .step e r h⟩

/-! ## Invariants as subsystems (§6.2) -/

/-- An inductive invariant restricts `S` to the worlds it admits. That the
    step can be typed on the subtype is exactly the obligation `h.step`. -/
def Inductive.restrict {S : Sys} {I : S.World → Prop} (h : Inductive S I) : Sys where
  World := {w // I w}
  Req := S.Req
  Res := S.Res
  Env := S.Env
  step e r w := ((S.step e r w.1).1, ⟨(S.step e r w.1).2, h.step e r w.1 w.2⟩)
  init w := S.init w.1

theorem Inductive.restrict_reachable {S : Sys} {I : S.World → Prop} (h : Inductive S I)
    {w : h.restrict.World} (hw : Reachable h.restrict w) : Reachable S w.1 := by
  induction hw with
  | init hi => exact .init hi
  | step e r _ ih => exact Reachable.step (S := S) e r ih

theorem Inductive.reachable_restrict {S : Sys} {I : S.World → Prop} (h : Inductive S I)
    {w : S.World} (hw : Reachable S w) : ∃ hI : I w, Reachable h.restrict ⟨w, hI⟩ := by
  induction hw with
  | init hi => exact ⟨h.init _ hi, .init hi⟩
  | step e r _ ih =>
    obtain ⟨hI, hr⟩ := ih
    exact ⟨_, Reachable.step (S := h.restrict) e r hr⟩

/-- An invariant of the restricted system is an invariant of `S` relative to
    `I`: this is how invariants proved on a subsystem transfer back. -/
theorem Inductive.lift_restrict {S : Sys} {I : S.World → Prop} (h : Inductive S I)
    {J : S.World → Prop} (hJ : Invariant h.restrict (fun w => J w.1)) : Invariant S J := by
  intro w hw
  obtain ⟨hI, hr⟩ := h.reachable_restrict hw
  exact hJ ⟨w, hI⟩ hr

/-! ## The canonical strengthening (§6.5) -/

/-- Worlds all of whose successors satisfy `X`. -/
def pre (S : Sys) (X : S.World → Prop) : S.World → Prop := fun w => ∀ e r, X (S.step e r w).2

theorem pre_mono {S : Sys} {X Y : S.World → Prop} (h : ∀ w, X w → Y w) (w : S.World) :
    pre S X w → pre S Y w := fun hx e r => h _ (hx e r)

/-- The first candidate strengthening the checker offers: `I ∧ pre I`
    (one step of k-induction). -/
def strengthen (S : Sys) (I : S.World → Prop) : S.World → Prop := fun w => I w ∧ pre S I w

/-- The weakest inductive invariant contained in `I`: every run from `w`
    stays in `I`. It is the greatest fixpoint of `X ↦ I ∧ pre X`. -/
def WeakestInductive (S : Sys) (I : S.World → Prop) : S.World → Prop :=
  fun w => ∀ w', ReachFrom S w w' → I w'

theorem WeakestInductive.sub {S : Sys} {I : S.World → Prop} {w : S.World} (h : WeakestInductive S I w) :
    I w := h w (.refl w)

theorem WeakestInductive.closed {S : Sys} {I : S.World → Prop} {w : S.World}
    (h : WeakestInductive S I w) : pre S (WeakestInductive S I) w :=
  fun e r w' hr => h w' (ReachFrom.first e r hr)

/-- The fixpoint equation: `WI = I ∧ pre WI`. -/
theorem WeakestInductive.unfold {S : Sys} {I : S.World → Prop} {w : S.World} :
    WeakestInductive S I w ↔ I w ∧ pre S (WeakestInductive S I) w := by
  constructor
  · intro h; exact ⟨h.sub, h.closed⟩
  · rintro ⟨hI, hp⟩ w' hr
    -- split the path at its first step
    suffices ∀ w', ReachFrom S w w' → w' = w ∨ WeakestInductive S I w' ∨
        ∃ e r, ReachFrom S (S.step e r w).2 w' by
      rcases this w' hr with rfl | hw | ⟨e, r, hr'⟩
      · exact hI
      · exact hw.sub
      · exact hp e r w' hr'
    intro w' hr
    induction hr with
    | refl => exact .inl rfl
    | step e r _ ih =>
      rcases ih with rfl | hw | ⟨e', r', hr'⟩
      · exact .inr (.inr ⟨e, r, .refl _⟩)
      · exact .inr (.inl (hw.closed e r))
      · exact .inr (.inr ⟨e', r', .step e r hr'⟩)

/-- Any `J ⊆ I` closed under steps is contained in the weakest inductive
    strengthening: nothing weaker than `WI` works. -/
theorem WeakestInductive.greatest {S : Sys} {I J : S.World → Prop} (hJI : ∀ w, J w → I w)
    (hJ : ∀ w, J w → pre S J w) {w : S.World} (hw : J w) : WeakestInductive S I w := by
  intro w' hr
  suffices J w' from hJI _ this
  induction hr with
  | refl => exact hw
  | step e r _ ih => exact hJ _ ih e r

theorem WeakestInductive.inductive {S : Sys} {I : S.World → Prop}
    (hinit : ∀ w, S.init w → WeakestInductive S I w) : Inductive S (WeakestInductive S I) :=
  ⟨hinit, fun e r _ h => h.closed e r⟩

/-- `I` is an invariant exactly when every initial world satisfies its
    weakest inductive strengthening. -/
theorem invariant_iff {S : Sys} {I : S.World → Prop} :
    Invariant S I ↔ ∀ w, S.init w → WeakestInductive S I w := by
  constructor
  · intro h w hi w' hr
    exact h w' (Reachable.of_reachFrom (.init hi) hr)
  · intro h
    exact Invariant.mono (Invariant.of_inductive (WeakestInductive.inductive h)) (fun _ hw => hw.sub)

/-- Every inductive strengthening sits inside `strengthen S I`, and so does
    the weakest one: `I ∧ pre I` never rules out a world that some
    inductive strengthening of `I` needs. -/
theorem WeakestInductive.sub_strengthen {S : Sys} {I : S.World → Prop} {w : S.World}
    (h : WeakestInductive S I w) : strengthen S I w :=
  ⟨h.sub, fun e r => (h.closed e r).sub⟩

/-- A counterexample to induction: a world satisfying `I` and a step that
    leaves `I`. -/
structure CTI (S : Sys) (I : S.World → Prop) where
  world : S.World
  env : S.Env
  req : S.Req
  holds : I world
  breaks : ¬ I (S.step env req world).2

theorem CTI.not_inductive {S : Sys} {I : S.World → Prop} (c : CTI S I) : ¬ Inductive S I :=
  fun h => c.breaks (h.step _ _ _ c.holds)

/-- A CTI from a reachable world refutes the invariant itself: no proof
    will help, `I` is false. -/
theorem CTI.not_invariant {S : Sys} {I : S.World → Prop} (c : CTI S I) (hr : Reachable S c.world) :
    ¬ Invariant S I :=
  fun h => c.breaks (h _ (.step c.env c.req hr))

/-- A CTI from a world outside the strengthening `J` is excluded by `J`:
    the diagnosis "strengthen `I` to exclude this world". -/
theorem CTI.excluded {S : Sys} {I J : S.World → Prop} (c : CTI S I) (hJ : Inductive S (fun w => I w ∧ J w)) :
    ¬ J c.world :=
  fun hj => c.breaks (hJ.step c.env c.req _ ⟨c.holds, hj⟩).1

end LeanApi.Props
