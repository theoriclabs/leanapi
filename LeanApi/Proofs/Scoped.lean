/-
  Reusable isolation theorem (M7): for ANY app built as
    route → authenticate → decode → load (scoped) → core → commit
  response noninterference follows from three app obligations:

  1. `load_view`: the scoped load depends only on the actor's view.
  2. `commit_view`: a commit's response depends only on the actor's view,
     and it maps view-equivalent worlds to view-equivalent worlds (for all
     observers).
  3. `auth_view`: authentication depends only on the part of the world every
     observer shares (sessions).

  `decode` and `core` are arbitrary pure functions: they need NO proof.
  That is the point: a new app states its policy as a view, proves the three
  obligations about its storage model, and gets `step_noninterference`.
  private-games instantiates this in `PrivateGames/Model/Generic.lean`.
-/
import LeanApi.Http.Router

namespace LeanApi.Proofs

universe u

/-- The shape of a scoped application's reference model. -/
structure ScopedApp where
  World : Type
  Actor : Type
  Op : Type
  Input : Type
  Need : Type
  Slice : Type
  Plan : Type
  /-- The observer relation: what `a` may observe of a world. -/
  SameView : Actor → World → World → Prop
  entries : List (Op × Method × List Seg)
  trailing : TrailingSlash := .redirect
  authenticate : Req → World → Except Res Actor
  decode : Op → Req → Except Res Input
  need : Input → Need
  load : Actor → World → Need → Slice
  core : Actor → Input → Slice → Plan
  run : Actor → Plan → World → Res × World

namespace ScopedApp

variable (A : ScopedApp)

def SameViews (w₁ w₂ : A.World) : Prop := ∀ a, A.SameView a w₁ w₂

def operate (op : A.Op) (r : Req) (w : A.World) : Res × A.World :=
  match A.authenticate r w with
  | .error res => (res, w)
  | .ok a =>
    match A.decode op r with
    | .error res => (res, w)
    | .ok i => A.run a (A.core a i (A.load a w (A.need i))) w

def step (r : Req) (w : A.World) : Res × A.World :=
  match Router.resolveIn A.entries A.trailing r with
  | .respond res => (res, w)
  | .route op ps => A.operate op { r with params := ps } w

/-- What an app must prove. -/
structure Obligations : Prop where
  auth_view : ∀ r w₁ w₂, A.SameViews w₁ w₂ → A.authenticate r w₁ = A.authenticate r w₂
  load_view : ∀ a w₁ w₂ n, A.SameView a w₁ w₂ → A.load a w₁ n = A.load a w₂ n
  run_view : ∀ a p w₁ w₂, A.SameViews w₁ w₂ →
    (A.run a p w₁).1 = (A.run a p w₂).1 ∧ A.SameViews (A.run a p w₁).2 (A.run a p w₂).2

theorem operate_noninterference (h : A.Obligations) (op : A.Op) (r : Req) {w₁ w₂ : A.World}
    (hw : A.SameViews w₁ w₂) :
    (A.operate op r w₁).1 = (A.operate op r w₂).1 ∧ A.SameViews (A.operate op r w₁).2 (A.operate op r w₂).2 := by
  unfold operate
  rw [h.auth_view r w₁ w₂ hw]
  cases A.authenticate r w₂ with
  | error res => exact ⟨rfl, hw⟩
  | ok a =>
    simp only
    cases A.decode op r with
    | error res => exact ⟨rfl, hw⟩
    | ok i =>
      simp only
      rw [h.load_view a w₁ w₂ _ (hw a)]
      exact h.run_view a _ w₁ w₂ hw

/-- **Generic isolation.** Any `ScopedApp` meeting the obligations has
    single-request response noninterference for every request. -/
theorem step_noninterference (h : A.Obligations) (r : Req) {w₁ w₂ : A.World} (hw : A.SameViews w₁ w₂) :
    (A.step r w₁).1 = (A.step r w₂).1 ∧ A.SameViews (A.step r w₁).2 (A.step r w₂).2 := by
  unfold step
  cases Router.resolveIn A.entries A.trailing r with
  | respond res => exact ⟨rfl, hw⟩
  | route op ps => exact A.operate_noninterference h op _ hw

/-- Unrouted requests never change the world, for any app. -/
theorem unrouted_pure (r : Req) (w : A.World) (res : Res)
    (h : Router.resolveIn A.entries A.trailing r = .respond res) : A.step r w = (res, w) := by
  simp [step, h]

end ScopedApp

end LeanApi.Proofs
