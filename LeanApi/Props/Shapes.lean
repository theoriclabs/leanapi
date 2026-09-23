/-
  Property shapes beyond state invariants (PLAN.md M12, PROPERTIES.md §3,
  §4, §6.1). Each is an invariant of a derived system, or reduces to one.

  * `Safe`: a selected request never changes the world.
  * Step properties (`StepProp`, `Monotone`, `Frame`): a relation between a
    world and its successor. `Sys.withPrev` is the transition-augmented
    system, and `stepProp_iff` states a step property as an invariant of it
    (§6.1). Step properties pull back along simulations.
  * `Enabled`: the positive twin of a restrictive property (§4.5).
  * `Observation`, `NI`, `Hidden`: noninterference over a projection, with
    the hiddenness witness that rules out review C1's vacuity (§5.2), and
    `NIPackage`, which cannot be built without an `Enabled` companion.
-/
import LeanApi.Props.Ops

namespace LeanApi.Props

open Sys

variable {S : Sys}

/-! ## Safe requests -/

/-- Requests selected by `sel` never change the world. -/
def Safe (S : Sys) (sel : S.Req → Prop) : Prop := ∀ e r w, sel r → (S.step e r w).2 = w

/-- A safe request preserves every invariant, with no proof about it. -/
theorem Safe.preserves {sel : S.Req → Prop} (h : Safe S sel) (I : S.World → Prop) :
    ∀ e r w, sel r → I w → I (S.step e r w).2 := fun e r w hs hw => by rw [h e r w hs]; exact hw

/-! ## Step properties and the transition-augmented system -/

/-- `P` relates every world to each of its successors. -/
def StepProp (S : Sys) (P : S.World → S.World → Prop) : Prop := ∀ e r w, P w (S.step e r w).2

/-- The same, only from reachable worlds. -/
def StepInv (S : Sys) (P : S.World → S.World → Prop) : Prop :=
  ∀ e r w, Reachable S w → P w (S.step e r w).2

theorem StepProp.stepInv {P : S.World → S.World → Prop} (h : StepProp S P) : StepInv S P :=
  fun e r w _ => h e r w

/-- The transition-augmented system: the world records the previous world
    (§6.1). Initially both components are the same initial world. -/
def Sys.withPrev (S : Sys) : Sys where
  World := S.World × S.World
  Req := S.Req
  Res := S.Res
  Env := S.Env
  step e r w := ((S.step e r w.2).1, (w.2, (S.step e r w.2).2))
  init w := S.init w.2 ∧ w.1 = w.2

theorem withPrev_reachable {w : S.withPrev.World} (h : Reachable S.withPrev w) : Reachable S w.2 := by
  induction h with
  | init hi => exact .init hi.1
  | step e r _ ih => exact .step (S := S) e r ih

/-- **Step properties are invariants of the augmented system.** A reflexive
    step property holds of every reachable transition exactly when "previous
    and current are related" is an invariant of `withPrev`. -/
theorem stepInv_iff {P : S.World → S.World → Prop} (hrefl : ∀ w, P w w) :
    StepInv S P ↔ Invariant S.withPrev (fun w => P w.1 w.2) := by
  constructor
  · intro h w hw
    cases hw with
    | init hi => rw [hi.2]; exact hrefl _
    | step e r hr => exact h e r _ (withPrev_reachable hr)
  · intro h e r w hw
    -- lift the reachable world into the augmented system
    have : ∀ w, Reachable S w → ∃ p, Reachable S.withPrev (p, w) := by
      intro w hw
      induction hw with
      | init hi => exact ⟨_, .init ⟨hi, rfl⟩⟩
      | step e r _ ih =>
        obtain ⟨p, hp⟩ := ih
        exact ⟨_, Reachable.step (S := S.withPrev) e r hp⟩
    obtain ⟨p, hp⟩ := this w hw
    exact h _ (Reachable.step (S := S.withPrev) e r hp)

/-- Step properties pull back along a simulation, when `P` is reflexive
    (stuttering steps relate a world to itself). -/
theorem StepProp.pullback {T : Sys} {f : S.World → T.World} {P : T.World → T.World → Prop}
    (hsim : Simulation S T f) (hrefl : ∀ x, P x x) (h : StepProp T P) :
    StepProp S (fun w w' => P (f w) (f w')) := by
  intro e r w
  rcases hsim.step e r w with hs | ⟨e', r', hs⟩
  · rw [hs]; exact hrefl _
  · rw [hs]; exact h e' r' (f w)

/-- A quantity only grows (for a preorder `le`). -/
def Monotone (S : Sys) {α : Type} (f : S.World → α) (le : α → α → Prop) : Prop :=
  StepProp S (fun w w' => le (f w) (f w'))

/-- Requests selected by `sel` leave the projection `untouched` unchanged. -/
def Frame (S : Sys) {β : Type} (sel : S.Req → Prop) (untouched : S.World → β) : Prop :=
  ∀ e r w, sel r → untouched (S.step e r w).2 = untouched w

theorem Safe.frame {sel : S.Req → Prop} {β : Type} (h : Safe S sel) (f : S.World → β) : Frame S sel f :=
  fun e r w hs => by rw [h e r w hs]

/-! ## Enabledness -/

/-- In worlds and requests satisfying `pre`, the response satisfies `ok`. -/
def Enabled (S : Sys) (pre : S.World → S.Req → Prop) (ok : S.Res → Prop) : Prop :=
  ∀ e w r, pre w r → ok (S.step e r w).1

/-! ## Noninterference over a projection -/

/-- What an observer may see, as **functions** (PROPERTIES.md §2): `SameView`
    is equality of `view`, so it is an equivalence by construction. -/
structure Observation (S : Sys) where
  Observer : Type
  View : Type
  Obs : Type
  view : Observer → S.World → View
  obs : Observer → S.Res → Obs

namespace Observation

variable (O : Observation S)

def SameView (a : O.Observer) (w₁ w₂ : S.World) : Prop := O.view a w₁ = O.view a w₂

theorem SameView.refl (a : O.Observer) (w : S.World) : O.SameView a w w := rfl
theorem SameView.symm {a : O.Observer} {w₁ w₂ : S.World} (h : O.SameView a w₁ w₂) : O.SameView a w₂ w₁ := Eq.symm h
theorem SameView.trans {a : O.Observer} {w₁ w₂ w₃ : S.World} (h₁ : O.SameView a w₁ w₂)
    (h₂ : O.SameView a w₂ w₃) : O.SameView a w₁ w₃ := Eq.trans h₁ h₂

/-- Single-step noninterference for observer `a`, on requests `acts a r w`
    (typically "authenticates as `a`"). The environment is shared. -/
def NI (acts : O.Observer → S.Req → S.World → Prop) : Prop :=
  ∀ a e r w₁ w₂, O.SameView a w₁ w₂ → acts a r w₁ → O.obs a (S.step e r w₁).1 = O.obs a (S.step e r w₂).1

/-- The unwinding form: the view relation is also preserved. -/
def NIUnwinding (acts : O.Observer → S.Req → S.World → Prop) : Prop :=
  ∀ a e r w₁ w₂, O.SameView a w₁ w₂ → acts a r w₁ →
    O.obs a (S.step e r w₁).1 = O.obs a (S.step e r w₂).1 ∧ O.SameView a (S.step e r w₁).2 (S.step e r w₂).2

/-- **Hiddenness witness** (§5.2): for every observer, two different worlds
    look the same. Without it, `NI` can hold because `view` is injective
    (review C1). -/
def Hidden : Prop := ∀ a, ∃ w₁ w₂, O.SameView a w₁ w₂ ∧ w₁ ≠ w₂

/-- An injective view has no hiddenness witness: this is exactly C1. -/
theorem not_hidden_of_injective (a : O.Observer) (hinj : ∀ w₁ w₂, O.view a w₁ = O.view a w₂ → w₁ = w₂) :
    ¬ O.Hidden := fun h => by
  obtain ⟨w₁, w₂, hv, hne⟩ := h a
  exact hne (hinj _ _ hv)

theorem NIUnwinding.ni {acts : O.Observer → S.Req → S.World → Prop} (h : O.NIUnwinding acts) : O.NI acts :=
  fun a e r w₁ w₂ hv ha => (h a e r w₁ w₂ hv ha).1

end Observation

/-- A noninterference claim that the library accepts as evidence.
    Besides `NI`, it must show that the claim is not vacuous in any of the
    ways a bare `NI` can be (review H2, eb67460):

    * `hidden`: for every observer, two different worlds they cannot tell
      apart **in which they send a request** (`acts`). This rules out
      `acts := False`, and a view that determines the world (review C1).
    * `enabled`: an availability companion stated on what the observer
      sees, whose precondition implies `acts`.
    * `enabledWitness`: that precondition holds somewhere, for every
      observer.
    * `refusal`: some acting request is *not* a success. This rules out a
      trivial success predicate (`ok := True`), so `enabled` says something.

    "Deny everything" satisfies `NI` but cannot supply `enabled` together
    with `enabledWitness`; "allow everything" cannot supply `refusal`. -/
structure NIPackage (S : Sys) (O : Observation S) where
  acts : O.Observer → S.Req → S.World → Prop
  ni : O.NI acts
  hidden : ∀ a, ∃ w₁ w₂ r, O.SameView a w₁ w₂ ∧ w₁ ≠ w₂ ∧ acts a r w₁
  ok : O.Observer → O.Obs → Prop
  enabledPre : O.Observer → S.World → S.Req → Prop
  enabled : ∀ a e w r, enabledPre a w r → acts a r w ∧ ok a (O.obs a (S.step e r w).1)
  enabledWitness : ∀ a, ∃ w r, enabledPre a w r
  refusal : ∃ a e w r, acts a r w ∧ ¬ ok a (O.obs a (S.step e r w).1)

namespace NIPackage

variable {S : Sys} {O : Observation S}

/-- A package's view is never injective: the plain hiddenness witness. -/
theorem toHidden (P : NIPackage S O) : O.Hidden := fun a =>
  let ⟨w₁, w₂, _, hv, hne, _⟩ := P.hidden a
  ⟨w₁, w₂, hv, hne⟩

/-- Every observer can act: the claim covers at least one request each. -/
theorem acts_nonempty (P : NIPackage S O) (a : O.Observer) : ∃ r w, P.acts a r w :=
  let ⟨_, _, r, _, _, h⟩ := P.hidden a
  ⟨r, _, h⟩

/-- The success predicate is not trivially true. -/
theorem ok_nontrivial (P : NIPackage S O) : ∃ a o, ¬ P.ok a o :=
  let ⟨a, e, w, r, _, h⟩ := P.refusal
  ⟨a, _, h⟩

end NIPackage

end LeanApi.Props

namespace LeanApi.Props

open Sys

variable {S : Sys}

/-! ## Traces: noninterference over request sequences, by unwinding -/

/-- Run a sequence of requests, keeping the final world. -/
def runTrace (S : Sys) : List (S.Env × S.Req) → S.World → S.World
  | [], w => w
  | (e, r) :: rs, w => runTrace S rs (S.step e r w).2

@[simp] theorem runTrace_nil (w : S.World) : runTrace S [] w = w := rfl
@[simp] theorem runTrace_cons (e : S.Env) (r : S.Req) (rs : List (S.Env × S.Req)) (w : S.World) :
    runTrace S ((e, r) :: rs) w = runTrace S rs (S.step e r w).2 := rfl

theorem runTrace_append (xs ys : List (S.Env × S.Req)) (w : S.World) :
    runTrace S (xs ++ ys) w = runTrace S ys (runTrace S xs w) := by
  induction xs generalizing w with
  | nil => rfl
  | cons x xs ih => obtain ⟨e, r⟩ := x; exact ih _

namespace Observation

variable (O : Observation S)

/-- The unwinding condition for observer `a`, restricted to the requests
    `allowed` may send: each such step preserves `a`'s view relation. -/
def ViewClosedOn (a : O.Observer) (allowed : S.Req → Prop) : Prop :=
  ∀ e r w₁ w₂, allowed r → O.SameView a w₁ w₂ → O.SameView a (S.step e r w₁).2 (S.step e r w₂).2

theorem runTrace_sameView {a : O.Observer} {allowed : S.Req → Prop} (hc : O.ViewClosedOn a allowed)
    (rs : List (S.Env × S.Req)) (hrs : ∀ x ∈ rs, allowed x.2) {w₁ w₂ : S.World}
    (h : O.SameView a w₁ w₂) : O.SameView a (runTrace S rs w₁) (runTrace S rs w₂) := by
  induction rs generalizing w₁ w₂ with
  | nil => exact h
  | cons x rs ih =>
    obtain ⟨e, r⟩ := x
    exact ih (fun y hy => hrs y (List.mem_cons_of_mem _ hy))
      (hc e r w₁ w₂ (hrs _ List.mem_cons_self) h)

/-- **Trace noninterference by unwinding.** If every request in a trace
    preserves observer `a`'s view relation, then at any point of the trace
    where `a` sends a request, `a` observes the same response from two
    worlds that started with the same view for `a`. -/
theorem trace_ni {acts : O.Observer → S.Req → S.World → Prop} (hni : O.NI acts) {a : O.Observer}
    {allowed : S.Req → Prop} (hc : O.ViewClosedOn a allowed) (pre : List (S.Env × S.Req))
    (hpre : ∀ x ∈ pre, allowed x.2) (e : S.Env) (r : S.Req) {w₁ w₂ : S.World}
    (h : O.SameView a w₁ w₂) (ha : acts a r (runTrace S pre w₁)) :
    O.obs a (S.step e r (runTrace S pre w₁)).1 = O.obs a (S.step e r (runTrace S pre w₂)).1 :=
  hni a e r _ _ (O.runTrace_sameView hc pre hpre h) ha

end Observation

end LeanApi.Props
