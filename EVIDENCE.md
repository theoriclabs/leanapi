# Evidence record: private-games on LeanAPI

Status as of LeanAPI 0.6.0. Required by DESIGN.md §8.4 and decision Q11.
The post (intent.md) should quote this file, not summarize it.

**The claim tables are generated** from the property registry in
[`PrivateGames/Evidence.lean`](examples/private-games/PrivateGames/Evidence.lean)
by `./scripts/gen_evidence.sh`, and CI fails if they drift
(`--check`). A **Proved** row can only be registered with theorems that
exist and pass the axiom rule below, so the tables cannot claim more than
the checked theorems say. The prose (scope, hidden data, assumptions, open
items) is hand-written.

Every claim below is one of:

- **Proved**: a Lean theorem, checked by `./scripts/axiom_audit.sh`. It uses no
  `sorry`, no `native_decide`, and no axioms beyond `propext`,
  `Classical.choice` and `Quot.sound`.
- **Checked**: a runtime test in `leanapi_tests`, run locally. CI execution
  for this working tree has not been verified.
- **Assumed**: trusted and not established here.
- **Open**: wanted, with neither a proof nor qualifying evidence.

## Scope

**Exported proved routes** (the domain of the theorems):

| Route | Operation |
|---|---|
| `POST /games` | OpenGame |
| `GET /games` | ListMyGames |
| `GET /games/{id}` | ReadGame |
| `POST /games/{id}/moves` | PlayMove |
| `POST /games/{id}/resignation` | Resign |

These run through `PrivateGames.App.decode` and `PrivateGames.App.core`,
which are the same functions in the native service and in the reference model
`PrivateGames.Model.step`.

**Unproved routes** on the same server: `POST /players` (register) and
`POST /sessions` (login). Both are plain M1 handlers that touch only the
player and token tables. They reveal whether a name is taken, by design.
`GET /healthz` and `/readyz` are answered by middleware.

## Claims

### 1. Isolation: no route leaks another user's games

<!-- BEGIN GENERATED: Isolation -->
| Claim | Status | Where |
|---|---|---|
| For a request that authenticates as `p`, only `p`'s view (sessions, visible games in order, own receipts, player ids, next id) matters for the complete response (status, all headers, body bytes), even if another player's view differs | **Proved** | `PrivateGames.Model.step_noninterference_caller`, `PrivateGames.Model.generic_isolation_caller` |
| If two worlds agree on every player's view, responses are identical and the successor worlds again agree | **Proved** | `PrivateGames.Model.step_noninterference` |
| The caller view is not vacuous: for every player, two different worlds look the same to them (hiddenness witness) | **Proved** | `PrivateGames.Model.gamesObs_hidden` |
| An observation whose view determines the world has no hiddenness witness (review C1); the search reports the all-players view as such | **Checked** | `LeanApi.Props.Observation.not_hidden_of_injective` (proved, generic); `tests/Tests/Props.lean` "hiddenness witness" (search) |
| A request that authenticates as `p` preserves `p`'s view in the successor worlds, even if other players' views differ | **Proved** | `PrivateGames.Model.step_view_caller` |
| Trace noninterference for a coalition: after any sequence of requests by coalition members, every member's response depends only on what the coalition can see together | **Proved** | `PrivateGames.Model.trace_noninterference`, `PrivateGames.Model.byCoalition_of_auth` |
| The per-caller claim as a library `NIPackage`, with every non-vacuity obligation discharged (for every player: a hidden difference in a world where they act, a successful read of their own game; and a refused read), given `ReadPlumbing`: some request routes to `GET /games/{id}`, decodes and carries a bearer token | **Proved** | `PrivateGames.Model.gamesNI`, `LeanApi.Props.NIPackage.acts_nonempty`, `LeanApi.Props.NIPackage.ok_nontrivial` |
| `ReadPlumbing` holds for a concrete request (`GET /games/1` with a bearer token) | **Checked** | `tests/Tests/Props.lean` "read plumbing" |
| Existence privacy: a game you do not participate in is indistinguishable from a game that does not exist | **Proved** | `PrivateGames.Model.existence_private` |
| The native repository puts the policy into the SQL predicate and re-checks it on the decoded row; other user's game ≡ missing id, byte for byte, for read, move and resign | **Checked** | `tests/Tests/Games.lean` §9.3 |
| SQLite's physical execution does not expose other rows | **Assumed** |  |
<!-- END GENERATED: Isolation -->

"Hidden data" means every game the caller does not participate in, plus
other players' receipts. The observation is the complete HTTP response.
**Not covered:** timing, logs, and the id sequence. A new game's id reveals
the total number of games; this is decision 0009's known release.

### 2. Idempotence

<!-- BEGIN GENERATED: Idempotence -->
| Claim | Status | Where |
|---|---|---|
| Immediate keyed replay after a successful write with a fresh key returns the recorded response with `Idempotent-Replayed: true` and leaves the model world unchanged | **Proved** | `PrivateGames.Model.keyed_replay` |
| Keyed replay after any sequence of intervening requests, from any player, returns the recorded response (marked) and changes nothing, in the model's own receipt path. Same premises as the immediate replay | **Proved** | `PrivateGames.Model.keyed_replay_after`, `PrivateGames.Model.step_receipts` |
| The same holds for any system wrapped by the library's `Keyed` transformer with a ledger satisfying `LedgerLaws`; private-games instantiated with the list ledger | **Proved** | `LeanApi.Props.Keyed.keyed_replay_after`, `LeanApi.Props.listLedger_laws`, `PrivateGames.Model.gamesKeyed_replay_after` |
| Reusing a key with different input is refused and changes nothing (`Keyed` wrapper over the model; the model's own `keyReused` branch has no separate theorem) | **Proved** | `PrivateGames.Model.gamesKeyed_reuse`, `LeanApi.Props.Keyed.keyed_reuse` |
| Reusing a key with different input is refused (422) natively | **Checked** | `tests/Tests/Games.lean` "keyed idempotence" |
| Resigning twice has the same domain state effect; the model's second unkeyed resignation leaves its state unchanged | **Proved** | `PrivateGames.resign_idem`, `PrivateGames.resign_resign`, `PrivateGames.Model.resign_state_idem` |
| Reads (`GET /games`, `GET /games/{id}`) never change the world, on any branch, and so preserve every invariant | **Proved** | `PrivateGames.Model.reads_safe`, `LeanApi.Proofs.ScopedApp.safe_of_pure_plans`, `PrivateGames.Model.reads_preserve` |
| Unrouted requests (404, 405, OPTIONS, redirects) never change the world | **Proved** | `PrivateGames.Model.unrouted_pure` |
| The receipt is written in the same transaction as the state change | **Checked** | "restart after commit" test |
| Concurrent submissions of one key produce one transition | **Checked** | "simultaneous moves" test |
<!-- END GENERATED: Idempotence -->

The contract (key scope, input identity, retention, replay after revocation)
is decision 0010.

### 3. Domain and system invariants

<!-- BEGIN GENERATED: Domain -->
| Claim | Status | Where |
|---|---|---|
| Accepted decisions are `Allowed`, follow `Transition`, and preserve `Valid` (the last generated by `preserves`) | **Proved** | `PrivateGames.decide_allowed`, `PrivateGames.decide_transition`, `PrivateGames.decide_valid`, `PrivateGames.Valid.preserved_playMove`, `PrivateGames.Valid.preserved_resign` |
| Non-participants are refused for every command | **Proved** | `PrivateGames.decide_nonparticipant` |
| Opening a game yields a valid game | **Proved** | `PrivateGames.Valid.preserved_openGame` |
| The runtime check `Valid.check` (run on every load and before every write) agrees with the proved `Valid` | **Proved** | `PrivateGames.Valid.check_iff`, `LeanApi.Props.StoredInvariant.guardWrite_ok`, `LeanApi.Props.StoredInvariant.guardLoad_ok` |
| Every stored game is `Valid`, in every reachable model world | **Proved** | `PrivateGames.Model.allValid` |
| Game ids are unique, in every reachable model world (with the strengthening: every id is below `nextGame`) | **Proved** | `PrivateGames.Model.uniqueIds`, `PrivateGames.Model.freshIds`, `PrivateGames.Model.uniqueIds_needs_fresh` |
| A game's move log only grows and its revision never decreases; games are never removed | **Proved** | `PrivateGames.Model.movesGrow` |
| Availability: a participant's read of their visible game succeeds with 200 and the game, through the full HTTP step | **Proved** | `PrivateGames.Model.read_available`, `PrivateGames.Model.gameRes_status`, `PrivateGames.Model.reads_own_enabled` |
| Stored values round-trip (`Cell`, `TimeControl`, `Nat` below 2^63) | **Proved** | `PrivateGames.Storage.cell_roundtrip`, `PrivateGames.Storage.timeControl_roundtrip`, `PrivateGames.Storage.nat_roundtrip` |
| A stored game that is not `Valid` is a typed error (500 without detail), never a crash | **Checked** | "stored row that fails validation" |
| Typed API (`PrivateGames/Api.lean`): GET and HEAD requests never change the state. Free for every typed API: each GET endpoint carries the proof, checked when it is built | **Proved** | `LeanApi.Api.step_safe`, `PrivateGames.Api.api_reads_safe` |
| Typed API: every stored game is `Valid`, ids are unique, and every id is below `nextGame`, in every reachable state. Per-endpoint obligations computed from the signatures; the writes are steps of the game store, whose writers are the domain decisions | **Proved** | `LeanApi.Api.inductive_of`, `PrivateGames.Api.api_allValid`, `PrivateGames.Api.api_uniqueIds`, `PrivateGames.Api.api_freshIds` |
| The typed API answers exactly as the reference model (status, ETag, Location, replay marker, Allow, WWW-Authenticate, body) on random request sequences, including every error status (401, 404, 405, 409, 412, 415, 422, 428) | **Checked** | `tests/Tests/Differential.lean` "typed API ≡ model" |
<!-- END GENERATED: Domain -->

### 4. Concurrency and consistency

<!-- BEGIN GENERATED: Concurrency -->
| Claim | Status | Where |
|---|---|---|
| Simultaneous moves on one revision: exactly one commits, the rest get 412 | **Checked** | "simultaneous moves" (8 concurrent) |
| A list's `total` and returned page use the same WAL snapshot, even if a writer commits between the two SQL statements | **Checked** | "list count and page share a WAL snapshot" |
| Revocation between admission and commit is refused at commit | **Checked** | "revocation between admission and commit" |
| Commits are serializable per game (single writer, `BEGIN IMMEDIATE`, compare-and-swap) | **Checked** | tests above; mechanism is decision 0008 |
| Concurrency in the model | **Open** |  |
<!-- END GENERATED: Concurrency -->

### 5. Reusable form and the property library

<!-- BEGIN GENERATED: Reusable -->
| Claim | Status | Where |
|---|---|---|
| Any `ScopedApp` whose authentication, scoped load and run response depend only on one caller's view has identical responses when only that view matches | **Proved** | `LeanApi.Proofs.ScopedApp.step_noninterference_caller` |
| Under the stronger premise that every actor's view matches, the relation is also preserved across one step | **Proved** | `LeanApi.Proofs.ScopedApp.step_noninterference` |
| private-games discharges both sets of obligations; its routed steps coincide with the M6 model | **Proved** | `PrivateGames.Model.gamesApp_caller_obligations`, `PrivateGames.Model.gamesApp_obligations`, `PrivateGames.Model.gamesApp_step_route` |
| A second app with a different policy (notes shared with other users) discharges both sets too | **Proved** | `Notes.Shared.callerObligations`, `Notes.Shared.isolation_caller`, `Notes.Shared.obligations`, `Notes.Shared.isolation` |
| Invariant kernel: `Inductive` gives `Invariant`; `I` is an invariant iff every initial world satisfies its weakest inductive strengthening; a counterexample to induction from a reachable world refutes `I` | **Proved** | `LeanApi.Props.Invariant.of_inductive`, `LeanApi.Props.invariant_iff`, `LeanApi.Props.CTI.not_invariant` |
| Entity invariants lift to the store with one obligation per writer kind; unique ids are inductive with `Fresh` and not without it | **Proved** | `LeanApi.Props.ListStore.allOf_inductive`, `LeanApi.Props.ListStore.ids_invariant`, `LeanApi.Props.ListStore.unique_not_inductive` |
| Invariants and step properties transfer along simulations; step properties are invariants of the transition-augmented system | **Proved** | `LeanApi.Props.Invariant.pullback`, `LeanApi.Props.StepProp.pullback`, `LeanApi.Props.stepInv_iff` |
| Trace noninterference follows from single-step NI plus the unwinding condition, for any system | **Proved** | `LeanApi.Props.Observation.trace_ni` |
| Typed middleware: `decorate` preserves status and body, a passing `guard` is transparent, and a `guard`'s refusal depends only on its declared observation | **Proved** | `LeanApi.Stage.decorate_preserves`, `LeanApi.Stage.guard_transparent`, `LeanApi.Stage.guard_observes` |
| Exported routes outside the proved set are reported, and tests fail on any not declared here | **Checked** | `Router.coverage`, `tests/Tests/Tier2.lean` |
| Every writer touching a table a system invariant is about is covered by its proof or listed as unproved; the build fails on drift | **Checked** | `#check_writer_coverage` in `PrivateGames/Evidence.lean` (a build-time check) |
<!-- END GENERATED: Reusable -->

## Assumptions (trusted base)

1. **Native ≡ model.** The native shell (`App/Service.lean`: load, commit
   and receipt through LeanDB) refines `Model.step`. Evidence: the
   differential test runs 400 random requests from 4 users against both and
   requires identical status, `ETag`, `Location`, `Allow`,
   `WWW-Authenticate`, replay marker and body. Mutation check: breaking the
   model's visibility filter makes the test fail with 63 mismatches.
   **Checked, not proved.**
2. **Authenticator contract** (decision 0003). A bearer token maps to the
   player its digest was issued for. Tokens are 256-bit random values, stored
   only as SHA-256 digests.
3. **Crypto** (decision 0002): OpenSSL 3 (SHA-256, HMAC, scrypt, RAND_bytes,
   constant-time compare), through leancrypto's C binding.
4. **`Std.Http`** parsing and framing (Lean toolchain v4.33.0), plus LeanAPI's
   head decoding (`Runtime/Server.lean`): the model receives the `Req` the
   edge built.
5. **Middleware** (decision 0001): `recover → requestId → accessLog → health
   → securityHeaders → timeout(10000ms)`. It is trusted adapter code. The
   access log records method, target, status, size, duration and client
   address, never bodies, headers or cookies.
6. **LeanDB and SQLite**: query translation, transactions, and WAL snapshot
   semantics. LeanDB's own query-model theorem does not cover generated SQL
   execution.
7. **The Lean compiler and runtime.**
8. **Deployment**: the running binary is built from this commit and exposes
   only this route table. Not checked.

## Open

- Trace noninterference when players **outside** the coalition also send
  requests. They can legitimately change what the coalition sees (an
  outsider opens a game with a member), so the claim needs a declassification
  rule for such writes (PROPERTIES.md P5).
- Proof (not test) that the native shell refines the model.
- Concurrency in the model.
- Receipt expiry.
- The keyed theorems are about the model (and the generic `Keyed`
  wrapper). That the LeanDB receipt table behaves like the model's receipt
  list (unique index on actor, op and key; written in the same
  transaction) is **checked** by the restart and concurrency tests, not
  proved.

## How to re-check

```bash
lake build
lake build leanapi_tests && ./.lake/build/bin/leanapi_tests
./scripts/axiom_audit.sh
./scripts/gen_evidence.sh --check     # claim tables match the registry
```

Specification files, kept separate from proofs so that a weakened spec shows
up as its own diff:

| Spec | File |
|---|---|
| `Valid` (declared with `invariant`), `Allowed`, `Transition`, `visible` | `examples/private-games/PrivateGames/Domain/Game.lean` |
| System invariants, simulation to the store of games | `examples/private-games/PrivateGames/Model/Invariants.lean` |
| Registered claims and writers | `examples/private-games/PrivateGames/Evidence.lean` |
| `SameView`, `SameViews` (the isolation observation) | `examples/private-games/PrivateGames/Model/Isolation.lean` (top) |
| `step`, `load`, `commit` (the model) | `examples/private-games/PrivateGames/Model/Step.lean` |
