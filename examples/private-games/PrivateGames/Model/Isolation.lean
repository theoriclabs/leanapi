/-
  Isolation (decision 0009): single-request response noninterference.

  Two worlds with the same view for the caller give the same response, and
  their successors again have the same view. The caller of a request is not
  known before authentication, so the view is stated for every player:
  hidden data is "games a player does not participate in, and other
  players' receipts". The main theorem is `step_noninterference`.
-/
import PrivateGames.Model.Step

namespace PrivateGames.Model

open LeanApi PrivateGames.App

/-- `w₁` and `w₂` look the same to player `p`. -/
structure SameView (p : PlayerId) (w₁ w₂ : World) : Prop where
  sessions : w₁.sessions = w₂.sessions
  games : visibleGames p w₁ = visibleGames p w₂
  receipts : ownReceipts p w₁ = ownReceipts p w₂
  players : w₁.players = w₂.players
  nextGame : w₁.nextGame = w₂.nextGame

/-- Same view for every player: what an unauthenticated request can differ on
    is nothing, and an authenticated one sees its own player's view. -/
def SameViews (w₁ w₂ : World) : Prop := ∀ p, SameView p w₁ w₂

theorem load_view {p : PlayerId} {w₁ w₂ : World} (h : SameView p w₁ w₂) (n : Need) :
    load p w₁ n = load p w₂ n := by
  simp only [load, h.games, h.receipts, h.players]

theorem authenticate_view {w₁ w₂ : World} (h : w₁.sessions = w₂.sessions) (r : Req) :
    authenticate r w₁ = authenticate r w₂ := by
  simp only [authenticate, h]

/-! ### Commits preserve the view -/

theorem visibleGames_append (p : PlayerId) (w : World) (g : Game) (ng : Nat) :
    visibleGames p { w with games := w.games ++ [g], nextGame := ng } =
      visibleGames p w ++ (if visible p g then [g] else []) := by
  simp [visibleGames, List.filter_append, List.filter_cons]

theorem ownReceipts_record (p q : PlayerId) (k : Option Keyed) (res : Res) (w : World) :
    ownReceipts q (recordReceipt p k res w) =
      ownReceipts q w ++ (match k with
        | some k => if p = q then [(⟨p, k.op, k.key⟩, Receipt.ofRes k.fingerprint res)] else []
        | none => []) := by
  cases k with
  | none => simp [recordReceipt]
  | some k =>
    simp only [recordReceipt, ownReceipts, List.filter_append, List.filter_cons, List.filter_nil]
    by_cases hpq : p = q <;> simp [hpq]

theorem visibleGames_record (q p : PlayerId) (k : Option Keyed) (res : Res) (w : World) :
    visibleGames q (recordReceipt p k res w) = visibleGames q w := by
  cases k <;> rfl

theorem record_fields (p : PlayerId) (k : Option Keyed) (res : Res) (w : World) :
    (recordReceipt p k res w).sessions = w.sessions ∧ (recordReceipt p k res w).players = w.players ∧
      (recordReceipt p k res w).nextGame = w.nextGame ∧ (recordReceipt p k res w).games = w.games := by
  cases k <;> exact ⟨rfl, rfl, rfl, rfl⟩

theorem recordReceipt_view {p q : PlayerId} {k : Option Keyed} {res : Res} {w₁ w₂ : World}
    (h : SameView q w₁ w₂) : SameView q (recordReceipt p k res w₁) (recordReceipt p k res w₂) := by
  obtain ⟨a1, b1, c1, d1⟩ := record_fields p k res w₁
  obtain ⟨a2, b2, c2, d2⟩ := record_fields p k res w₂
  refine ⟨by rw [a1, a2]; exact h.sessions, ?_, ?_, by rw [b1, b2]; exact h.players,
    by rw [c1, c2]; exact h.nextGame⟩
  · rw [visibleGames_record, visibleGames_record]; exact h.games
  · rw [ownReceipts_record, ownReceipts_record, h.receipts]

/-- Mapping a game that `p` can see: another player `q` sees the same
    change in both worlds as long as they agreed before. -/
theorem visible_map (q : PlayerId) (old new : Game) (gs : List Game)
    (hvis : visible q old = visible q new) :
    (gs.map fun g => if g = old then new else g).filter (visible q) =
      (gs.filter (visible q)).map (fun g => if g = old then new else g) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases hg : g = old
    · subst hg; simp [List.filter_cons, hvis, ih]
      split <;> simp_all
    · simp [List.filter_cons, hg, ih]
      split <;> simp_all

/-- A game `q` cannot see is untouched in `q`'s view. -/
theorem visible_map_hidden (q : PlayerId) (old new : Game) (gs : List Game)
    (h1 : visible q old = false) (h2 : visible q new = false) :
    (gs.map fun g => if g = old then new else g).filter (visible q) = gs.filter (visible q) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases hg : g = old
    · subst hg; simp [h1, h2, ih]
    · simp [List.filter_cons, hg, ih]

/-- Transitions never change participants, so visibility is preserved. -/
theorem playMove_participants {p : PlayerId} {e : Revision} {c : Cell} {g g' : Game}
    (h : PrivateGames.playMove p e c g = .ok g') : g'.x = g.x ∧ g'.o = g.o := by
  obtain ⟨_, _, _, _, _, rfl⟩ := playMove_ok h; exact ⟨rfl, rfl⟩

end PrivateGames.Model

namespace PrivateGames.Model

open LeanApi PrivateGames.App

theorem visible_eq_of_participants {q : PlayerId} {a b : Game} (hx : b.x = a.x) (ho : b.o = a.o) :
    visible q a = visible q b := by
  simp [visible, Game.isParticipant, hx, ho]

theorem commitOk_view {p : PlayerId} {old new : Game} {w₁ w₂ : World} (h : SameView p w₁ w₂) :
    commitOk p old new w₁ = commitOk p old new w₂ := by
  simp only [commitOk, h.games]

theorem SameView.refl (p : PlayerId) (w : World) : SameView p w w := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem commit_noninterference (p : PlayerId) (wr : Write) (k : Option Keyed) (build : Game → Res)
    {w₁ w₂ : World} (h : SameViews w₁ w₂) :
    (commit p wr k build w₁).1 = (commit p wr k build w₂).1 ∧
      SameViews (commit p wr k build w₁).2 (commit p wr k build w₂).2 := by
  cases wr with
  | insertGame g =>
    have hn := (h p).nextGame
    simp only [commit, hn]
    refine ⟨trivial, fun q => recordReceipt_view ?_⟩
    refine ⟨(h q).sessions, ?_, (h q).receipts, (h q).players, by simp⟩
    rw [visibleGames_append, visibleGames_append, (h q).games]
  | updateGame old new =>
    simp only [commit, commitOk_view (h p)]
    split
    · rename_i hok
      refine ⟨rfl, fun q => recordReceipt_view ?_⟩
      simp only [commitOk, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨_, _⟩, hx⟩, ho⟩ := hok
      have hvis := visible_eq_of_participants (q := q) hx ho
      refine ⟨(h q).sessions, ?_, (h q).receipts, (h q).players, (h q).nextGame⟩
      show (w₁.games.map _).filter (visible q) = (w₂.games.map _).filter (visible q)
      rw [visible_map q old new _ hvis, visible_map q old new _ hvis]
      exact congrArg _ (h q).games
    · exact ⟨rfl, h⟩

theorem runPlan_noninterference (p : PlayerId) (plan : Plan) {w₁ w₂ : World} (h : SameViews w₁ w₂) :
    (runPlan p plan w₁).1 = (runPlan p plan w₂).1 ∧ SameViews (runPlan p plan w₁).2 (runPlan p plan w₂).2 := by
  cases plan with
  | respond r => exact ⟨rfl, h⟩
  | write wr k build => exact commit_noninterference p wr k build h

theorem operate_noninterference (op : Op) (r : Req) {w₁ w₂ : World} (h : SameViews w₁ w₂) :
    (operate op r w₁).1 = (operate op r w₂).1 ∧ SameViews (operate op r w₁).2 (operate op r w₂).2 := by
  have hs : w₁.sessions = w₂.sessions := (h default).sessions
  unfold operate
  rw [authenticate_view hs]
  cases authenticate r w₂ with
  | error res => exact ⟨rfl, h⟩
  | ok p =>
    simp only
    cases decode op r with
    | error res => exact ⟨rfl, h⟩
    | ok i =>
      simp only
      rw [load_view (h p)]
      exact runPlan_noninterference p _ h

/-- **Isolation.** For every request to the exported proved routes: if two
    worlds agree on every player's view (differing only in data hidden from
    each player), the response is identical (status, headers, body) and the
    successor worlds again agree on every player's view. -/
theorem step_noninterference (r : Req) {w₁ w₂ : World} (h : SameViews w₁ w₂) :
    (step r w₁).1 = (step r w₂).1 ∧ SameViews (step r w₁).2 (step r w₂).2 := by
  unfold step
  cases Router.resolveIn entries .redirect r with
  | respond res => exact ⟨rfl, h⟩
  | route op ps => exact operate_noninterference op _ h

/-- The per-caller form: hidden data is anything outside `p`'s view, and a
    world may differ from another arbitrarily there. Holding only `p`'s view
    fixed is enough for any request that authenticates as `p`. -/
theorem step_noninterference_caller (r : Req) (p : PlayerId) {w₁ w₂ : World} (h : SameView p w₁ w₂)
    (hp : authenticate r w₁ = .ok p) : (step r w₁).1 = (step r w₂).1 := by
  unfold step
  cases Router.resolveIn entries .redirect r with
  | respond res => rfl
  | route op ps =>
    simp only
    unfold operate
    have ha : authenticate { r with params := ps } w₁ = .ok p := by
      rw [← hp]; simp [authenticate, authDigest, Req.header?, bearerToken?]
    rw [ha, ← authenticate_view h.sessions, ha]
    simp only
    cases decode op { r with params := ps } with
    | error res => rfl
    | ok i =>
      simp only
      rw [load_view h]
      -- the response of a commit depends only on p's view
      cases core p i (load p w₂ i.need) with
      | respond res => rfl
      | write wr k build =>
        cases wr with
        | insertGame g => simp only [runPlan, commit, h.nextGame]
        | updateGame old new =>
          simp only [runPlan, commit, commitOk_view h]
          split <;> rfl

end PrivateGames.Model
