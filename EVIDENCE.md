# Evidence record: private-games on LeanAPI

Status as of LeanAPI 0.4.0, 2026-09-22. Required by DESIGN.md §8.4 and
decision Q11. The post (intent.md) should quote this file, not summarize it.

Every claim below is one of:

- **Proved**: a Lean theorem, checked by `./scripts/axiom_audit.sh`. It uses no
  `sorry`, no `native_decide`, and no axioms beyond `propext`,
  `Classical.choice` and `Quot.sound`.
- **Checked**: a runtime test in `leanapi_tests` (CI).
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

| Claim | Status | Where |
|---|---|---|
| For any request, two worlds that agree on every player's view (sessions, visible games in order, own receipts, player ids, next id) produce **identical responses** (status, all headers, body bytes), and their successor worlds again agree | **Proved** | `PrivateGames.Model.step_noninterference` |
| Per caller: for a request that authenticates as `p`, only `p`'s view matters | **Proved** | `step_noninterference_caller` |
| Existence privacy: a game you do not participate in is indistinguishable from a game that does not exist | **Proved** | `existence_private` |
| The model reads only visible games, own receipts and player ids (restricted logical reads) | **Proved**, by construction of `Model.load` (the only data access in `operate`) | `PrivateGames/Model/Step.lean` |
| The native repository puts the policy into the SQL predicate (`x = actor OR o = actor`) and re-checks it on the decoded row | **Checked** (tests: other user's game ≡ missing id, byte for byte, for read, move and resign) | `tests/Tests/Games.lean` §9.3 |
| SQLite's physical execution does not expose other rows | **Assumed** | |

"Hidden data" means every game the caller does not participate in, plus
other players' receipts. The observation is the complete HTTP response.
**Not covered:** timing, logs, and the id sequence. A new game's id reveals
the total number of games; this is decision 0009's known release.

### 2. Idempotence

| Claim | Status | Where |
|---|---|---|
| Keyed replay: after a keyed command commits with response `res`, sending the same request again returns `res` marked `Idempotent-Replayed: true` and leaves the world unchanged. Holds for every route and input | **Proved** | `PrivateGames.Model.keyed_replay` |
| A different input under the same key is refused (422) and changes nothing | **Proved** in `core` (`withReceipt`); **checked** natively | `tests/Tests/Games.lean` "keyed idempotence" |
| Resign twice has the same state effect as once, with or without a key | **Proved** | `PrivateGames.resign_idem`, `resign_resign`, `Model.resign_state_idem` |
| Reads (`GET /games`, `GET /games/{id}`) never change the world, on any branch | **Proved** | `Model.reads_pure` |
| Unrouted requests (404, 405, OPTIONS, redirects) never change the world | **Proved** | `Model.unrouted_pure` |
| The receipt is written in the same transaction as the state change | **Checked**: restart after commit, then retry returns the receipt and the move is applied once | "restart after commit" test |
| Concurrent submissions of one key produce one transition | **Checked** (6 concurrent requests, one revision bump) | "simultaneous moves" test |

The contract (key scope, input identity, retention, replay after revocation)
is decision 0010.

### 3. Domain

| Claim | Status | Where |
|---|---|---|
| Accepted decisions are `Allowed`, follow `Transition`, and preserve `Valid` | **Proved** | `decide_allowed`, `decide_transition`, `decide_valid` |
| Non-participants are refused for every command | **Proved** | `decide_nonparticipant` |
| Opening a game yields a valid game | **Proved** | `openGame_valid` |
| Availability: a participant's read of their visible game succeeds with 200 and the game | **Proved** | `Model.read_available`, `gameRes_status` |
| Stored values round-trip (`Cell`, `TimeControl`, `Nat` below 2^63) | **Proved** | `Storage.cell_roundtrip`, `timeControl_roundtrip`, `nat_roundtrip` |
| A stored game that is not `Valid` is a typed error (500 without detail), never a crash | **Checked** | "stored row that fails validation" |

### 4. Concurrency and consistency

| Claim | Status | Where |
|---|---|---|
| Simultaneous moves on one revision: exactly one commits, the rest get 412 | **Checked** (8 concurrent) | "simultaneous moves" |
| Revocation between admission and commit is refused at commit | **Checked** | "revocation between admission and commit" |
| Commits are serializable per game (single writer, `BEGIN IMMEDIATE`, compare-and-swap) | **Checked** above; mechanism is decision 0008 | |
| The model is sequential; concurrency is not modelled | **Open** | |

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

- Trace noninterference across request sequences and several actors.
- Proof (not test) that the native shell refines the model.
- Concurrency in the model.
- Receipt expiry.
- Build-time report of routes outside the proved set (M7).

## How to re-check

```bash
lake build
lake build leanapi_tests && ./.lake/build/bin/leanapi_tests
./scripts/axiom_audit.sh
```

Specification files, kept separate from proofs so that a weakened spec shows
up as its own diff:

| Spec | File |
|---|---|
| `Valid`, `Allowed`, `Transition`, `visible` | `examples/private-games/PrivateGames/Domain/Game.lean` |
| `SameView`, `SameViews` (the isolation observation) | `examples/private-games/PrivateGames/Model/Isolation.lean` (top) |
| `step`, `load`, `commit` (the model) | `examples/private-games/PrivateGames/Model/Step.lean` |
