/-
  Domain-level theorems (PLAN.md M3.1).

  * `playMove_valid`, `resign_valid`: accepted decisions preserve `Valid`.
  * `playMove_allowed`, `resign_allowed`: accepted ⇒ `Allowed`.
  * `playMove_transition`, `resign_transition`: accepted ⇒ `Transition`.
  * `resign_idem`: resigning twice has the same state effect as once.
  * `openGame_valid`.
-/
import PrivateGames.Domain.Game

namespace PrivateGames

open Game

theorem take_append_single {α} (l : List α) (a : α) (k : Nat) (hk : k ≤ l.length) :
    (l ++ [a]).take k = l.take k := List.take_append_of_le_length hk

theorem legalHistory_snoc (ms : List Cell) (c : Cell)
    (h : Rules.legalHistory ms = true) (hw : Rules.winner? ms = none) :
    Rules.legalHistory (ms ++ [c]) = true := by
  unfold Rules.legalHistory at *
  simp only [List.all_eq_true, List.mem_range, List.length_append, List.length_singleton] at *
  intro k hk
  by_cases hlt : k < ms.length
  · rw [take_append_single ms c k (Nat.le_of_lt hlt)]
    exact h k hlt
  · have : k = ms.length := by omega
    subst this
    rw [take_append_single ms c ms.length (Nat.le_refl _), List.take_length, hw]
    rfl

theorem outcome_ongoing {g : Game} (h : g.outcome = .ongoing) :
    g.resigned = none ∧ Rules.winner? g.moves = none ∧ g.moves.length < 9 := by
  unfold Game.outcome at h
  cases hr : g.resigned with
  | some p => simp [hr] at h
  | none =>
    simp only [hr] at h
    cases hw : Rules.winner? g.moves with
    | some m => simp [hw] at h
    | none =>
      simp only [hw] at h
      refine ⟨rfl, rfl, ?_⟩
      split at h
      · assumption
      · simp at h

theorem isFree_nodup {g : Game} {c : Cell} (hn : (g.moves.map (·.i)).Nodup) (hf : g.isFree c = true) :
    ((g.moves ++ [c]).map (·.i)).Nodup := by
  simp only [List.map_append, List.map_cons, List.map_nil]
  rw [List.nodup_append]
  refine ⟨hn, by simp, ?_⟩
  intro a ha b hb heq
  simp only [List.mem_singleton] at hb
  subst hb heq
  simp only [Game.isFree, Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hf
  obtain ⟨x, hx, hxi⟩ := List.mem_map.mp ha
  exact hf x hx hxi

theorem playMove_ok {p : PlayerId} {e : Revision} {c : Cell} {g g' : Game}
    (h : playMove p e c g = .ok g') :
    g.isParticipant p = true ∧ g.rev = e ∧ g.outcome = .ongoing ∧ g.toMove = p ∧
      g.isFree c = true ∧ g' = { g with moves := g.moves ++ [c], rev := g.rev + 1 } := by
  unfold playMove at h
  by_cases h1 : g.isParticipant p = true <;> simp [h1] at h
  by_cases h2 : g.rev = e <;> simp [h2] at h
  by_cases h3 : g.outcome = .ongoing <;> simp [h3] at h
  by_cases h4 : g.toMove = p <;> simp [h4] at h
  by_cases h5 : g.isFree c = true <;> simp [h5] at h
  subst h2
  exact ⟨h1, rfl, h3, h4, h5, h.symm⟩

theorem playMove_valid {p : PlayerId} {e : Revision} {c : Cell} {g g' : Game}
    (v : Valid g) (h : playMove p e c g = .ok g') : Valid g' := by
  obtain ⟨_, _, hon, _, hfree, rfl⟩ := playMove_ok h
  obtain ⟨hres, hwin, hlen⟩ := outcome_ongoing hon
  refine ⟨v.distinct, isFree_nodup v.nodup hfree, legalHistory_snoc _ _ v.history hwin, ?_, ?_, ?_⟩
  · simp; omega
  · have := v.rev; simp [hres] at this ⊢; omega
  · intro q hq; simp [hres] at hq

theorem playMove_allowed {p : PlayerId} {e : Revision} {c : Cell} {g g' : Game}
    (h : playMove p e c g = .ok g') : Allowed p g (.play e c) := by
  obtain ⟨h1, _, h3, h4, _, _⟩ := playMove_ok h
  exact ⟨h1, h3, h4⟩

theorem playMove_transition {p : PlayerId} {e : Revision} {c : Cell} {g g' : Game}
    (h : playMove p e c g = .ok g') : Transition p g (.play e c) g' := by
  obtain ⟨_, _, _, _, _, h6⟩ := playMove_ok h
  exact h6

/-- A refused decision changes nothing: `playMove` has no state to change
    on refusal, which is what `Except` gives by construction. The runtime
    counterpart (no commit on refusal) is proved of the model in M6. -/
theorem playMove_rev {p : PlayerId} {e : Revision} {c : Cell} {g g' : Game}
    (h : playMove p e c g = .ok g') : g'.rev = g.rev + 1 ∧ g.rev = e := by
  obtain ⟨_, h2, _, _, _, rfl⟩ := playMove_ok h
  exact ⟨rfl, h2⟩

theorem resign_ok {p : PlayerId} {g g' : Game} (h : resign p g = .ok g') :
    g.isParticipant p = true ∧
      ((g.resigned = some p ∧ g' = g) ∨
       (g.resigned ≠ some p ∧ g.outcome = .ongoing ∧ g' = { g with resigned := some p, rev := g.rev + 1 })) := by
  unfold resign at h
  by_cases h1 : g.isParticipant p = true <;> simp [h1] at h
  refine ⟨h1, ?_⟩
  by_cases h2 : g.resigned = some p <;> simp [h2] at h
  · exact .inl ⟨h2, h.symm⟩
  · by_cases h3 : g.outcome = .ongoing <;> simp [h3] at h
    exact .inr ⟨h2, h3, h.symm⟩

theorem participant_cases {g : Game} {p : PlayerId} (h : g.isParticipant p = true) : p = g.x ∨ p = g.o := by
  simp [Game.isParticipant] at h; exact h

theorem resign_valid {p : PlayerId} {g g' : Game} (v : Valid g) (h : resign p g = .ok g') : Valid g' := by
  obtain ⟨hp, hcase⟩ := resign_ok h
  rcases hcase with ⟨_, rfl⟩ | ⟨_, hon, rfl⟩
  · exact v
  · obtain ⟨hres, _, _⟩ := outcome_ongoing hon
    refine ⟨v.distinct, v.nodup, v.history, v.length, ?_, ?_⟩
    · have := v.rev; simp [hres] at this ⊢; omega
    · intro q hq; simp at hq; subst hq; exact participant_cases hp

theorem resign_allowed {p : PlayerId} {g g' : Game} (h : resign p g = .ok g') : Allowed p g .resign :=
  (resign_ok h).1

theorem resign_transition {p : PlayerId} {g g' : Game} (h : resign p g = .ok g') :
    Transition p g .resign g' := by
  obtain ⟨_, hcase⟩ := resign_ok h
  rcases hcase with ⟨h1, h2⟩ | ⟨_, h3, h4⟩
  · exact .inl ⟨h1, h2⟩
  · exact .inr ⟨h3, h4⟩

/-- State idempotence of `Resign`: after an accepted resignation, resigning
    again is accepted and leaves the game unchanged. -/
theorem resign_idem {p : PlayerId} {g g' : Game} (h : resign p g = .ok g') : resign p g' = .ok g' := by
  obtain ⟨hp, hcase⟩ := resign_ok h
  rcases hcase with ⟨hr, rfl⟩ | ⟨_, _, rfl⟩
  · exact h
  · unfold resign; simp [Game.isParticipant] at hp ⊢; rcases hp with hp | hp <;> simp [hp]

/-- The same, as a composition law: `resign >=> resign = resign`. -/
theorem resign_resign (p : PlayerId) (g : Game) : (resign p g >>= resign p) = resign p g := by
  cases h : resign p g with
  | error e => rfl
  | ok g' => simp only [bind, Except.bind]; exact resign_idem h

theorem openGame_valid {id : GameId} {p o : PlayerId} {tc : TimeControl} {g : Game}
    (h : openGame id p o tc = .ok g) : Valid g := by
  unfold openGame at h
  by_cases hpo : p = o <;> simp [hpo] at h
  subst h
  exact ⟨hpo, List.nodup_nil, rfl, by simp [Game.opened], by simp [Game.opened], by simp [Game.opened]⟩

theorem decide_valid {p : PlayerId} {g g' : Game} {cmd : Command} (v : Valid g)
    (h : PrivateGames.decide p g cmd = .ok g') : Valid g' := by
  cases cmd with
  | play e c => exact playMove_valid v h
  | resign => exact resign_valid v h

theorem decide_allowed {p : PlayerId} {g g' : Game} {cmd : Command}
    (h : PrivateGames.decide p g cmd = .ok g') : Allowed p g cmd := by
  cases cmd with
  | play e c => exact playMove_allowed h
  | resign => exact resign_allowed h

theorem decide_transition {p : PlayerId} {g g' : Game} {cmd : Command}
    (h : PrivateGames.decide p g cmd = .ok g') : Transition p g cmd g' := by
  cases cmd with
  | play e c => exact playMove_transition h
  | resign => exact resign_transition h

/-- Non-participants are always refused, whatever the command. -/
theorem decide_nonparticipant {p : PlayerId} {g : Game} (cmd : Command) (h : g.isParticipant p = false) :
    PrivateGames.decide p g cmd = .error .notParticipant := by
  cases cmd <;> simp [PrivateGames.decide, playMove, resign, h]

end PrivateGames
