/-
  The business rule, stated once and proved: you see a user exactly when
  they are on your team. Change who may see what in `Schema.lean`, and this
  file stops compiling until the rule is restated here, where a reviewer
  sees it.
-/
import TeamsDemo.Schema

namespace TeamsDemo

open LeanDb PolicyView

/-- LeanDB compares references by their stored id. -/
theorem ref_beq_iff {α : Type} (a b : Ref α) : (a == b) = true ↔ a = b := by
  change (a.toInt64 == b.toInt64) = true ↔ a = b
  rw [beq_iff_eq]
  constructor
  · intro h; cases a; cases b; simp_all
  · intro h; rw [h]

/-- **You see a user exactly when they are on your team.** -/
theorem sees_iff_same_team (me : Me) (u : Stored UserRow) :
    Policy.rule (s := TeamsDb) me u = true ↔ u.val.team = tref me.team := by
  simp [Policy.rule, ref_beq_iff]

end TeamsDemo
