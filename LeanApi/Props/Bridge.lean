/-
  Bridge (PROPERTIES.md P1): every `ScopedApp` is a `Sys`. `ScopedApp`
  stays the pipeline-specific signature that makes isolation proofs cheap;
  `Sys` is where the generic invariant theory lives. Decision 0016.
-/
import LeanApi.Proofs.Scoped
import LeanApi.Props.Sys

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
