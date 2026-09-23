/-
  Bridge (PROPERTIES.md P1): every `ScopedApp` is a `Sys`. `ScopedApp`
  stays the pipeline-specific signature that makes isolation proofs cheap;
  `Sys` is where the generic invariant theory lives. Decision 0016.
-/
import LeanApi.Proofs.Scoped
import LeanApi.Props.Shapes

namespace LeanApi.Proofs.ScopedApp

open LeanApi.Props

/-- A scoped app as a transition system with no environment. The initial
    worlds are the app's choice (for example, "no games yet"). -/
def toSys (A : ScopedApp) (init : A.World → Prop) : Sys where
  World := A.World
  Req := Req
  Res := Res
  Env := Unit
  step _ r w := A.step r w
  init := init

@[simp] theorem toSys_step (A : ScopedApp) (init : A.World → Prop) (e : Unit) (r : Req) (w : A.World) :
    (A.toSys init).step e r w = A.step r w := rfl

end LeanApi.Proofs.ScopedApp

namespace LeanApi.Proofs.ScopedApp

open LeanApi.Props

/-- Plans that never change the world (for example "respond"). The app
    proves `run_pure` once for its plan type. -/
structure PurePlans (A : ScopedApp) where
  pure : A.Plan → Prop
  run_pure : ∀ a p w, pure p → (A.run a p w).2 = w

/-- **`Safe` from the plan type.** If every plan `core` produces for the
    operations `ops` is pure, requests routed to `ops` are `Safe`: this
    holds on every branch (auth failure, decode failure, any decision). -/
theorem safe_of_pure_plans (A : ScopedApp) (init : A.World → Prop) (P : A.PurePlans) (ops : A.Op → Prop)
    (hcore : ∀ op a i s r, ops op → A.decode op r = .ok i → P.pure (A.core a i s)) :
    Safe (A.toSys init) (fun r => ∃ op ps, Router.resolveIn A.entries A.trailing r = .route op ps ∧ ops op) := by
  rintro _ r w ⟨op, ps, hroute, hop⟩
  show (A.step r w).2 = w
  simp only [step, hroute, operate]
  cases A.authenticate { r with params := ps } w with
  | error _ => rfl
  | ok a =>
    simp only
    cases hd : A.decode op { r with params := ps } with
    | error _ => rfl
    | ok i => exact P.run_pure a _ w (hcore op a i _ _ hop hd)

end LeanApi.Proofs.ScopedApp
