/-
  Isolation for the typed private-games API, through the framework's
  `Api.noninterference`: for a request authenticated as player `p`, the
  whole response (status, headers, body) depends only on what `p` may see
  (`Model.SameView`: sessions, `p`'s visible games in order, `p`'s own
  receipts, player ids, the next id). Other players' games may differ
  arbitrarily.

  The obligation is per endpoint and computed from its signature: every
  input is extracted alike in both states (automatic for inputs that do
  not read the state; the session lookup for `Auth`), and the body answers
  alike in states that look the same to the authenticated player.
-/
import PrivateGames.ApiProofs
import PrivateGames.Model.Existence

namespace PrivateGames.Api

open LeanApi LeanApi.Props PrivateGames PrivateGames.App PrivateGames.Model

/-- The relation isolation is stated against: `p`'s view, and a request
    that authenticates as `p`. -/
def AsP (p : PlayerId) : Rel World := fun env r s₁ s₂ =>
  SameView p s₁ s₂ ∧ gamesAuth.authenticate s₁ env r = .ok p

/-! ## Authentication reads only the sessions -/

theorem auth_congr {w₁ w₂ : World} (h : w₁.sessions = w₂.sessions) (env : Env) (r : Req) :
    gamesAuth.authenticate w₁ env r = gamesAuth.authenticate w₂ env r := by
  obtain ⟨g₁, s₁, p₁, r₁, n₁⟩ := w₁
  obtain ⟨g₂, s₂, p₂, r₂, n₂⟩ := w₂
  simp only at h
  subst h
  rfl

/-! ## Handler bodies answer alike in states that look the same -/

theorem receiptOf_view {p : PlayerId} {w₁ w₂ : World} (h : SameView p w₁ w₂) (k : Keyed) :
    receiptOf p w₁ k = receiptOf p w₂ k := by
  simp only [receiptOf, h.receipts]

/-- A keyed write answers alike when the receipts and the decision's answer
    agree; the new store does not matter. -/
theorem keyed_answer [ToResponse α] {p : PlayerId} {w₁ w₂ : World} (h : SameView p w₁ w₂)
    (k? : Option Keyed) (decide : World → Decided α) (hd : (decide w₁).result = (decide w₂).result) :
    (keyed p k? decide w₁).2 = (keyed p k? decide w₂).2 := by
  unfold keyed
  have hr : ∀ k, receiptOf p w₁ k = receiptOf p w₂ k := receiptOf_view h
  simp only [hr]
  split
  · rfl
  · revert hd
    cases decide w₁ <;> cases decide w₂ <;> simp [Decided.result] <;> intros <;> subst_vars <;> rfl

theorem openGame_answer {me : Auth PlayerId} {w₁ w₂ : World} (h : SameView me.val w₁ w₂)
    (body : Body OpenBody) (key : KeyHeader) :
    (openGame me body key w₁).2 = (openGame me body key w₂).2 := by
  apply keyed_answer h
  simp only [h.players, h.nextGame]
  split
  · rfl
  · split <;> rfl

theorem playMove_answer {me : Auth PlayerId} {w₁ w₂ : World} (h : SameView me.val w₁ w₂)
    (rev : IfMatchRequired ETagRev) (body : Body MoveBody) (id : Path GameId) (key : KeyHeader) :
    (playMove me rev body id key w₁).2 = (playMove me rev body id key w₂).2 := by
  apply keyed_answer h
  simp only [h.games]
  split
  · rfl
  · split <;> rfl

theorem resign_answer {me : Auth PlayerId} {w₁ w₂ : World} (h : SameView me.val w₁ w₂)
    (id : Path GameId) (key : KeyHeader) :
    (resign me id key w₁).2 = (resign me id key w₂).2 := by
  apply keyed_answer h
  simp only [h.games]
  split
  · rfl
  · split
    · rfl
    · rfl
    · split <;> rfl

/-! ## Every endpoint discharges its obligation -/

theorem stable_rfl {α : Type} [F : FromRequest World α] (hF : ∀ s₁ s₂ env r, F.extract s₁ env r = F.extract s₂ env r)
    (R : Rel World) : FromRequest.Stable (α := α) R :=
  fun env r s₁ s₂ _ => hF s₁ s₂ env r

/-- Authentication is stable, and it narrows the relation to the actor. -/
theorem auth_parts (p : PlayerId) :
    (∀ env r s₁ s₂, AsP p env r s₁ s₂ → gamesAuth.authenticate s₁ env r = gamesAuth.authenticate s₂ env r) ∧
    (∀ env r s₁ s₂ a, AsP p env r s₁ s₂ → gamesAuth.authenticate s₁ env r = .ok a → SameView a s₁ s₂) := by
  refine ⟨fun env r s₁ s₂ h => auth_congr h.1.sessions env r, fun env r s₁ s₂ a h ha => ?_⟩
  rw [h.2] at ha
  cases ha
  exact h.1

theorem api_isolated (p : PlayerId) : ∀ e ∈ gamesApi, e.Isolated (AsP p) := by
  intro e he
  simp only [gamesApi, List.mem_cons, List.not_mem_nil, or_false] at he
  have ⟨ha, hc⟩ := auth_parts p
  rcases he with rfl | rfl | rfl | rfl | rfl
  · -- openGame: Auth → Body → Header → Writes
    exact ⟨ha, hc, fun a => ⟨fun _ _ _ _ _ => rfl, ⟨fun _ _ _ _ _ => rfl, trivial⟩,
      fun body => ⟨fun _ _ _ _ _ => rfl, trivial, fun key _ _ s₁ s₂ h => by
        rw [openGame_answer h.2 body key]⟩⟩⟩
  · -- listGames: Auth → Query → Reads
    exact ⟨ha, hc, fun a => ⟨fun _ _ _ _ _ => rfl, trivial, fun q _ _ s₁ s₂ h => by
      simp only [listGames, h.2.games]⟩⟩
  · -- readGame: Auth → Path → Reads
    exact ⟨ha, hc, fun a => ⟨trivial, fun gid _ _ s₁ s₂ h => by
      simp only [readGame, h.2.games]⟩⟩
  · -- playMove: Auth → IfMatchRequired → Body → Path → Header → Writes
    exact ⟨ha, hc, fun a => ⟨fun _ _ _ _ _ => rfl, ⟨fun _ _ _ _ _ => rfl, ⟨fun _ _ _ _ _ => rfl, trivial⟩⟩,
      fun rev => ⟨fun _ _ _ _ _ => rfl, ⟨fun _ _ _ _ _ => rfl, trivial⟩,
        fun body => ⟨⟨fun _ _ _ _ _ => rfl, trivial⟩, fun gid => ⟨fun _ _ _ _ _ => rfl, trivial,
          fun key _ _ s₁ s₂ h => by rw [playMove_answer h.2 rev body ⟨gid⟩ key]⟩⟩⟩⟩⟩
  · -- resign: Auth → Path → Header → Writes
    exact ⟨ha, hc, fun a => ⟨⟨fun _ _ _ _ _ => rfl, trivial⟩, fun gid => ⟨fun _ _ _ _ _ => rfl, trivial,
      fun key _ _ s₁ s₂ h => by rw [resign_answer h.2 ⟨gid⟩ key]⟩⟩⟩

/-! ## The theorems -/

/-- **Isolation on the typed API.** For a request that authenticates as `p`,
    the complete response depends only on `p`'s view: another player's games
    and receipts may differ arbitrarily. -/
theorem api_noninterference (p : PlayerId) (env : Env) (r : Req) {w₁ w₂ : World}
    (hv : SameView p w₁ w₂) (ha : gamesAuth.authenticate w₁ env r = .ok p) :
    (gamesApi.step env r w₁).1 = (gamesApi.step env r w₂).1 :=
  Api.noninterference (A := gamesAuth) (V := gamesView) gamesApi p (api_isolated p) env r hv ha

/-- **Existence privacy on the typed API.** A game `p` does not play in is
    indistinguishable, to `p`, from no game at all. -/
theorem api_existence_private (p : PlayerId) (env : Env) (r : Req) (w : World) (g : Game)
    (hg : visible p g = false) (ha : gamesAuth.authenticate w env r = .ok p) :
    (gamesApi.step env r w).1 = (gamesApi.step env r (withHidden w g)).1 :=
  api_noninterference p env r (withHidden_view w g hg) ha

end PrivateGames.Api
