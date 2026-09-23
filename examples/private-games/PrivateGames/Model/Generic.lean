/-
  private-games as an instance of the reusable `LeanApi.Proofs.ScopedApp`
  (M7). The app-specific proof work is only the three obligations, all
  discharged by lemmas about the storage model. The generic theorem then
  gives isolation, and `step_eq` shows the instance IS the model M6 proved
  things about.
-/
import LeanApi.Proofs.Scoped
import PrivateGames.Model.Isolation

namespace PrivateGames.Model

open LeanApi LeanApi.Proofs PrivateGames.App

def gamesApp : ScopedApp where
  World := World
  Actor := PlayerId
  Op := Op
  Input := Input
  Need := Need
  Slice := Slice
  Plan := Plan
  SameView := SameView
  entries := entries
  authenticate := authenticate
  decode := decode
  need := Input.need
  load := load
  core := core
  run := runPlan

theorem gamesApp_obligations : gamesApp.Obligations where
  auth_view r _ _ h := authenticate_view (h (⟨0⟩ : PlayerId)).sessions r
  load_view _ _ _ n h := load_view h n
  run_view a p _ _ h := runPlan_noninterference a p h

/-- Operations agree with the M6 model, branch for branch. -/
theorem gamesApp_operate_eq (op : Op) (r : Req) (w : World) : gamesApp.operate op r w = operate op r w := by
  simp only [ScopedApp.operate, operate, gamesApp]
  split <;> split <;> simp_all

/-- For every request the instance's `step` and M6's `step` agree on each
    routed branch; unrouted branches are identical responses. -/
theorem gamesApp_step_route (r : Req) (w : World) (op : Op) (ps : List (String × String))
    (h : Router.resolveIn entries .redirect r = .route op ps) :
    step r w = gamesApp.operate op { r with params := ps } w := by
  rw [gamesApp_operate_eq]; simp [step, h]

/-- Obligations discharged: private-games gets isolation from the generic
    theorem with no further proof. -/
theorem generic_isolation (r : Req) {w₁ w₂ : World} (h : SameViews w₁ w₂) :
    (gamesApp.step r w₁).1 = (gamesApp.step r w₂).1 ∧
      gamesApp.SameViews (gamesApp.step r w₁).2 (gamesApp.step r w₂).2 :=
  gamesApp.step_noninterference gamesApp_obligations r h

end PrivateGames.Model
