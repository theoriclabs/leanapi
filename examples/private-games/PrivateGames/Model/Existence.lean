/-
  Existence privacy (decision 0009) as a direct corollary: adding a game the
  caller does not participate in is invisible to the caller.

  This also shows `SameView` is not vacuous: the two worlds below really
  differ (one has an extra game), yet the caller's responses coincide.
-/
import PrivateGames.Model.Isolation

namespace PrivateGames.Model

open LeanApi PrivateGames.App

/-- Add a game that `p` does not participate in. -/
def withHidden (w : World) (g : Game) : World := { w with games := w.games ++ [g] }

theorem withHidden_view {p : PlayerId} (w : World) (g : Game) (hg : visible p g = false) :
    SameView p w (withHidden w g) := by
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  simp [visibleGames, withHidden, List.filter_append, hg]

/-- **Existence privacy.** For any request that authenticates as `p`, a world
    containing an extra game `p` cannot see answers exactly as the world
    without it. In particular `GET /games/{id}` on a hidden game and on a
    nonexistent id are indistinguishable. -/
theorem existence_private (r : Req) (p : PlayerId) (w : World) (g : Game)
    (hg : visible p g = false) (hp : authenticate r w = .ok p) :
    (step r w).1 = (step r (withHidden w g)).1 :=
  step_noninterference_caller r p (withHidden_view w g hg) hp

/-- Every refusal that concerns a game the caller cannot see is the one fixed
    `hidden` response, whatever the game's contents. -/
theorem hidden_is_constant : hidden = Problem.notFound.toRes := rfl

end PrivateGames.Model
