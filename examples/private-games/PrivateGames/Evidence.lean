/-
  The evidence registry for private-games (PLAN.md M11).

  Every claim in EVIDENCE.md's tables is registered here. A **Proved**
  claim names its theorems, and `register_property` refuses a theorem that
  depends on `sorry`, `native_decide` or a non-standard axiom, so the
  generated tables cannot claim more than the checked theorems say.
  `scripts/gen_evidence.sh` splices `#evidence_tables` into EVIDENCE.md, and
  CI fails if the committed file differs.

  Writers (every route, job and admin command that changes state) are
  declared with the tables they touch. `#check_writer_coverage` fails the
  build if a writer touches a table that a registered system invariant is
  about but is neither covered by its proof nor listed as unproved.
-/
import PrivateGames.Model.Shapes
import PrivateGames.Model.Existence
import PrivateGames.Storage.Schema
import Notes.Shared

namespace PrivateGames.Evidence

open LeanApi LeanApi.Props PrivateGames.App

/-! ## Writers -/

declare_tables "games", "receipts", "players", "tokens"

-- The proved routes run through `Model.step`.
declare_writer "openGame" touches "games", "receipts"
declare_writer "listGames" readonly
declare_writer "readGame" readonly
declare_writer "playMove" touches "games", "receipts"
declare_writer "resign" touches "games", "receipts"
-- Unproved M1 handlers (EVIDENCE.md "Unproved routes").
declare_writer "POST /players" touches "players"
declare_writer "POST /sessions" touches "tokens"

/-- The writers of the model system: exactly the route table `entries` is
    compiled from, which is what `Model.step` routes through. An
    `Invariant gamesSys I` proof covers these and nothing else. -/
instance : HasWriters PrivateGames.Model.gamesSys := ⟨routeTable.map (·.1.name)⟩

/-! ## 1. Isolation -/

register_property "Isolation" "For a request that authenticates as `p`, only `p`'s view (sessions, visible games in order, own receipts, player ids, next id) matters for the complete response (status, all headers, body bytes), even if another player's view differs"
  proved by PrivateGames.Model.step_noninterference_caller, PrivateGames.Model.generic_isolation_caller shape "relational"
register_property "Isolation" "If two worlds agree on every player's view, responses are identical and the successor worlds again agree"
  proved by PrivateGames.Model.step_noninterference shape "relational"
register_property "Isolation" "The caller view is not vacuous: for every player, two different worlds look the same to them (hiddenness witness)"
  proved by PrivateGames.Model.gamesObs_hidden shape "relational"
register_property "Isolation" "An observation whose view determines the world has no hiddenness witness (review C1); the search reports the all-players view as such"
  checked at "`LeanApi.Props.Observation.not_hidden_of_injective` (proved, generic); `tests/Tests/Props.lean` \"hiddenness witness\" (search)"
register_property "Isolation" "A request that authenticates as `p` preserves `p`'s view in the successor worlds, even if other players' views differ"
  proved by PrivateGames.Model.step_view_caller shape "relational"
register_property "Isolation" "Trace noninterference for a coalition: after any sequence of requests by coalition members, every member's response depends only on what the coalition can see together"
  proved by PrivateGames.Model.trace_noninterference, PrivateGames.Model.byCoalition_of_auth shape "trace"
register_property "Isolation" "The per-caller claim as a library `NIPackage`, with every non-vacuity obligation discharged (for every player: a hidden difference in a world where they act, a successful read of their own game; and a refused read), given `ReadPlumbing`: some request routes to `GET /games/{id}`, decodes and carries a bearer token"
  proved by PrivateGames.Model.gamesNI, LeanApi.Props.NIPackage.acts_nonempty, LeanApi.Props.NIPackage.ok_nontrivial shape "relational"
register_property "Isolation" "`ReadPlumbing` holds for a concrete request (`GET /games/1` with a bearer token)"
  checked at "`tests/Tests/Props.lean` \"read plumbing\""
register_property "Isolation" "Existence privacy: a game you do not participate in is indistinguishable from a game that does not exist"
  proved by PrivateGames.Model.existence_private shape "relational"
register_property "Isolation" "The native repository puts the policy into the SQL predicate and re-checks it on the decoded row; other user's game ≡ missing id, byte for byte, for read, move and resign"
  checked at "`tests/Tests/Games.lean` §9.3"
register_property "Isolation" "SQLite's physical execution does not expose other rows" assumed

/-! ## 2. Idempotence -/

register_property "Idempotence" "Immediate keyed replay after a successful write with a fresh key returns the recorded response with `Idempotent-Replayed: true` and leaves the model world unchanged"
  proved by PrivateGames.Model.keyed_replay shape "two-step"
register_property "Idempotence" "Keyed replay after any sequence of intervening requests, from any player, returns the recorded response (marked) and changes nothing, in the model's own receipt path. Same premises as the immediate replay"
  proved by PrivateGames.Model.keyed_replay_after, PrivateGames.Model.step_receipts shape "trace"
register_property "Idempotence" "The same holds for any system wrapped by the library's `Keyed` transformer with a ledger satisfying `LedgerLaws`; private-games instantiated with the list ledger"
  proved by LeanApi.Props.Keyed.keyed_replay_after, LeanApi.Props.listLedger_laws, PrivateGames.Model.gamesKeyed_replay_after shape "trace"
register_property "Idempotence" "Reusing a key with different input is refused and changes nothing (`Keyed` wrapper over the model; the model's own `keyReused` branch has no separate theorem)"
  proved by PrivateGames.Model.gamesKeyed_reuse, LeanApi.Props.Keyed.keyed_reuse shape "step"
register_property "Idempotence" "Reusing a key with different input is refused (422) natively"
  checked at "`tests/Tests/Games.lean` \"keyed idempotence\""
register_property "Idempotence" "Resigning twice has the same domain state effect; the model's second unkeyed resignation leaves its state unchanged"
  proved by PrivateGames.resign_idem, PrivateGames.resign_resign, PrivateGames.Model.resign_state_idem shape "two-step"
register_property "Idempotence" "Reads (`GET /games`, `GET /games/{id}`) never change the world, on any branch, and so preserve every invariant"
  proved by PrivateGames.Model.reads_safe, LeanApi.Proofs.ScopedApp.safe_of_pure_plans, PrivateGames.Model.reads_preserve shape "step"
register_property "Idempotence" "Unrouted requests (404, 405, OPTIONS, redirects) never change the world"
  proved by PrivateGames.Model.unrouted_pure shape "step"
register_property "Idempotence" "The receipt is written in the same transaction as the state change"
  checked at "\"restart after commit\" test"
register_property "Idempotence" "Concurrent submissions of one key produce one transition"
  checked at "\"simultaneous moves\" test"

/-! ## 3. Domain and system invariants -/

register_property "Domain" "Accepted decisions are `Allowed`, follow `Transition`, and preserve `Valid` (the last generated by `preserves`)"
  proved by PrivateGames.decide_allowed, PrivateGames.decide_transition, PrivateGames.decide_valid, PrivateGames.Valid.preserved_playMove, PrivateGames.Valid.preserved_resign shape "step"
register_property "Domain" "Non-participants are refused for every command"
  proved by PrivateGames.decide_nonparticipant
register_property "Domain" "Opening a game yields a valid game"
  proved by PrivateGames.Valid.preserved_openGame
register_property "Domain" "The runtime check `Valid.check` (run on every load and before every write) agrees with the proved `Valid`"
  proved by PrivateGames.Valid.check_iff, LeanApi.Props.StoredInvariant.guardWrite_ok, LeanApi.Props.StoredInvariant.guardLoad_ok
register_invariant "Domain" "Every stored game is `Valid`, in every reachable model world"
  by PrivateGames.Model.allValid touches "games"
register_invariant "Domain" "Game ids are unique, in every reachable model world (with the strengthening: every id is below `nextGame`)"
  by PrivateGames.Model.uniqueIds, PrivateGames.Model.freshIds, PrivateGames.Model.uniqueIds_needs_fresh touches "games"
register_property "Domain" "A game's move log only grows and its revision never decreases; games are never removed"
  proved by PrivateGames.Model.movesGrow shape "step"
register_property "Domain" "Availability: a participant's read of their visible game succeeds with 200 and the game, through the full HTTP step"
  proved by PrivateGames.Model.read_available, PrivateGames.Model.gameRes_status, PrivateGames.Model.reads_own_enabled shape "enabled"
register_property "Domain" "Stored values round-trip (`Cell`, `TimeControl`, `Nat` below 2^63)"
  proved by PrivateGames.Storage.cell_roundtrip, PrivateGames.Storage.timeControl_roundtrip, PrivateGames.Storage.nat_roundtrip
register_property "Domain" "A stored game that is not `Valid` is a typed error (500 without detail), never a crash"
  checked at "\"stored row that fails validation\""

/-! ## 4. Concurrency -/

register_property "Concurrency" "Simultaneous moves on one revision: exactly one commits, the rest get 412"
  checked at "\"simultaneous moves\" (8 concurrent)"
register_property "Concurrency" "A list's `total` and returned page use the same WAL snapshot, even if a writer commits between the two SQL statements"
  checked at "\"list count and page share a WAL snapshot\""
register_property "Concurrency" "Revocation between admission and commit is refused at commit"
  checked at "\"revocation between admission and commit\""
register_property "Concurrency" "Commits are serializable per game (single writer, `BEGIN IMMEDIATE`, compare-and-swap)"
  checked at "tests above; mechanism is decision 0008"
register_property "Concurrency" "Concurrency in the model" unproved

/-! ## 5. Reusable form -/

register_property "Reusable" "Any `ScopedApp` whose authentication, scoped load and run response depend only on one caller's view has identical responses when only that view matches"
  proved by LeanApi.Proofs.ScopedApp.step_noninterference_caller shape "relational"
register_property "Reusable" "Under the stronger premise that every actor's view matches, the relation is also preserved across one step"
  proved by LeanApi.Proofs.ScopedApp.step_noninterference shape "relational"
register_property "Reusable" "private-games discharges both sets of obligations; its routed steps coincide with the M6 model"
  proved by PrivateGames.Model.gamesApp_caller_obligations, PrivateGames.Model.gamesApp_obligations, PrivateGames.Model.gamesApp_step_route
register_property "Reusable" "A second app with a different policy (notes shared with other users) discharges both sets too"
  proved by Notes.Shared.callerObligations, Notes.Shared.isolation_caller, Notes.Shared.obligations, Notes.Shared.isolation
register_property "Reusable" "Invariant kernel: `Inductive` gives `Invariant`; `I` is an invariant iff every initial world satisfies its weakest inductive strengthening; a counterexample to induction from a reachable world refutes `I`"
  proved by LeanApi.Props.Invariant.of_inductive, LeanApi.Props.invariant_iff, LeanApi.Props.CTI.not_invariant
register_property "Reusable" "Entity invariants lift to the store with one obligation per writer kind; unique ids are inductive with `Fresh` and not without it"
  proved by LeanApi.Props.ListStore.allOf_inductive, LeanApi.Props.ListStore.ids_invariant, LeanApi.Props.ListStore.unique_not_inductive
register_property "Reusable" "Invariants and step properties transfer along simulations; step properties are invariants of the transition-augmented system"
  proved by LeanApi.Props.Invariant.pullback, LeanApi.Props.StepProp.pullback, LeanApi.Props.stepInv_iff
register_property "Reusable" "Trace noninterference follows from single-step NI plus the unwinding condition, for any system"
  proved by LeanApi.Props.Observation.trace_ni
register_property "Reusable" "Typed middleware: `decorate` preserves status and body, a passing `guard` is transparent, and a `guard`'s refusal depends only on its declared observation"
  proved by LeanApi.Stage.decorate_preserves, LeanApi.Stage.guard_transparent, LeanApi.Stage.guard_observes
register_property "Reusable" "Exported routes outside the proved set are reported, and tests fail on any not declared here"
  checked at "`Router.coverage`, `tests/Tests/Tier2.lean`"
register_property "Reusable" "Every writer touching a table a system invariant is about is covered by its proof or listed as unproved; the build fails on drift"
  checked at "`#check_writer_coverage` in `PrivateGames/Evidence.lean` (a build-time check)"

#check_writer_coverage

end PrivateGames.Evidence
