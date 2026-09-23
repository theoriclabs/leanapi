/-
  Registry regressions (M11): removing a theorem or adding an uncovered
  writer must fail. `#guard_msgs` pins the exact failures.
-/
import PrivateGames.Evidence

namespace Tests.Registry

open LeanApi.Props

theorem cheat : 1 = 2 := by sorry

/-- error: register_property: `Tests.Registry.cheat` cannot be evidence for a proved claim: it depends on [sorryAx] -/
#guard_msgs (error, drop warning) in
register_property "Test" "one is two" proved by cheat

/-- error: Unknown constant `PrivateGames.Model.removedTheorem` -/
#guard_msgs (error) in
register_property "Test" "a removed theorem" proved by PrivateGames.Model.removedTheorem

/-- error: register_property: a proved claim must name its theorem(s) with `by` -/
#guard_msgs (error) in
register_property "Test" "a claim with no proof" proved

declare_writer "adminResetGame" touches "games"

/-- error: writer coverage failed:
writer `adminResetGame` touches [games] but is not covered by the proof of "Every stored game is `Valid`, in every reachable model world" (`PrivateGames.Model.allValid`) and is not listed as unproved for it
writer `adminResetGame` touches [games] but is not covered by the proof of "Game ids are unique, in every reachable model world (with the strengthening: every id is below `nextGame`)" (`PrivateGames.Model.uniqueIds`, `PrivateGames.Model.freshIds`, `PrivateGames.Model.uniqueIds_needs_fresh`) and is not listed as unproved for it -/
#guard_msgs (error) in
#check_writer_coverage

end Tests.Registry
