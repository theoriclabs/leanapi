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

/-! Review H5 (eb67460): coverage metadata is derived, not asserted. -/

/-- error: register_invariant: `Nat.add_comm` does not state `Invariant S I`, so it is not a system invariant; list it after one that is, or use `register_property` -/
#guard_msgs (error) in
register_invariant "Test" "Every stored game is Valid (forged)" by Nat.add_comm touches "games"

/-- error: declare_writer `adminWipe`: unknown table `everything`; declare it with `declare_tables` (known: games, receipts, players, tokens) -/
#guard_msgs (error) in
declare_writer "adminWipe" touches "everything"

/-- error: register_invariant: unknown table `nonexistent_table`; declare it with `declare_tables` (known: games, receipts, players, tokens) -/
#guard_msgs (error) in
register_invariant "Test" "valid again" by PrivateGames.Model.allValid touches "nonexistent_table"

/-- error: register_invariant: `unproved` names `nobody`, which is not a declared writer -/
#guard_msgs (error) in
register_invariant "Test" "valid again" by PrivateGames.Model.allValid touches "games" unproved "nobody"

-- The `unproved` clause parses (review M1) and lets coverage pass.
register_invariant "Test" "valid, admin reset excepted" by PrivateGames.Model.allValid
  touches "games" unproved "adminResetGame"

open Lean in
run_cmd do
  let some e := (LeanApi.Props.allProperties (← getEnv)).find? (·.claim == "valid, admin reset excepted")
    | throwError "not registered"
  unless e.covers.toList == ["openGame", "listGames", "readGame", "playMove", "resign"] do
    throwError "covers not derived from the route table: {e.covers}"
  unless (e.row.splitOn "not covering: `adminResetGame`").length == 2 do
    throwError "row does not name the unproved writer: {e.row}"

end Tests.Registry
