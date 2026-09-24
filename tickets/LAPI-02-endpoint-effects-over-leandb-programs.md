# LAPI-02: Endpoint effects over LeanDB programs: `Read s` and `Txn s ε`

**Repo:** theoriclabs/leanapi · **Area:** `LeanApi/Http/Endpoint.lean`, runtime · **Priority:** P0 · **Size:** L
**Depends on:** LeanDB M14 (`DbState`, `Read`/`Txn` programs with their meaning and execution, typed failures). **Enables:** LAPI-03, LAPI-05, LAPI-06.

## Problem

A typed endpoint's effect today is `Reads σ α := σ → α` or `Writes σ α := σ → σ × α`, run against a `Store σ` (`Endpoint.lean`: `Store`, `Reads`, `Writes`). `Store` needs the whole state as one Lean value, which a LeanDB database is not. So an API that should run on LeanDB has to be written twice:
- a typed API over an in-memory `World` (`PrivateGames/Api.lean`), which the proofs are about;
- a native service over LeanDB (`App/Service.lean`, `Storage/Repo.lean`), only checked against it.

LeanDB M14 provides the missing piece: programs as values. `Read s α` has no write constructor and no failure. `Txn s ε α` declares its failure type and is all or nothing. Both have a pure meaning over `DbState s` and an execution against SQLite (QUERIES.md §3).

## Proposal

**Effects.** Add `Handler` instances for LeanDB programs, next to the in-memory ones:

| Return type | `Effect` | Answers |
|---|---|---|
| `Read s ρ` | `.reads` | `ToResponse ρ` (typically `ρ = Except ε α`, with `ToProblem ε`) |
| `Txn s ε ρ` | `.writes` | commit: `ToResponse ρ`; abort with `e : ε`: `ToProblem ε`, with every write discarded |

**Laws, restated over the meaning.** `step` is defined by `Read.denote`/`Txn.denote` over `DbState s`, so the existing laws keep their shape:
- `step_safe`: a `Read` never changes the state (no write constructor).
- `Preserved I h`: for a `Txn`, its meaning preserves `I` on every state satisfying it (and `WF`).
- `Isolated R h`: for `Read`/`Txn`, the response is equal in `R`-related states.

**Authentication over the database.** `Authenticates.sessions` and `passwords` take a *read program* for the lookup (`fun t => lookup TokenRow.byDigest (digest t)`) instead of a function over an in-memory state. The whole request, authentication included, stays one pure function of `DbState`.

**The API's meaning.** `Api.step` and `Api.toSys` are defined over `DbState s` for LeanDB-backed APIs, so `Api.step_safe`, `Api.inductive_of` and `Api.noninterference` apply unchanged.

**Runtime.**
- `Api.serveDb (api : Api (DbState s)) (db : LeanDb connection handle) (stack)` runs each request's program in one LeanDB transaction:
  - an endpoint whose effect is `.reads` runs on a reader connection under the read snapshot;
  - `.writes` runs on the writer under `BEGIN IMMEDIATE`, with authentication in the same transaction.
- Each request gets a fresh `Env` (randomness, time), as today.
- A `DbFault` (lock timeout, I/O, corruption) aborts the request with no effect and answers 503, logged with the request id.

The in-memory `Store σ` effects stay supported. Notes keeps using them.

## Acceptance criteria

- A test schema (two entities, a unique index, a reference) with one `Read` endpoint and one `Txn` endpoint, served by `Api.serveDb` against SQLite, answers correctly over HTTP.
- `Api.step_safe`, `Api.inductive_of` and `Api.noninterference` instantiated for that API, with no `sorry`.
- `api!` still checks path arity and route conflicts, and `Api.describe` prints `Read s …`/`Txn s ε …` signatures.
- A `GET` endpoint returning a `Txn` does not compile (its effect is `.writes`).

## Tests

- **Abort discards writes.** A `Txn` that inserts, then throws: the insert is not visible afterwards, and the response is the `ToProblem` of the thrown value.
- **Fault leaves no trace.** A fault injected during a `Txn` (a busy writer with a zero timeout) answers 503, and the database is unchanged.
- **One snapshot per read.** A `Read` whose two queries straddle a concurrent commit sees both from the same snapshot.
- **Authentication in the same transaction.** A token revoked by one request is refused by the next, never used by a write that started after the revocation committed.

## Compatibility

Additive: the `Store`-based `Reads`/`Writes` are unchanged. Existing typed APIs keep working.

## Status (2026-09-23): done on LeanDB M14b (`d33d067`, pinned by commit)

Branch `lapi-02-read-effects` (name predates the write half), stacked on LAPI-04.

`LeanApi/Http/DbEndpoint.lean`:
- `Handler (DbState s) (Read s ρ)` (effect `.reads`) and `Handler (DbState s) (Tx s ε ρ)` (effect `.writes`; `Tx s ε ρ := (σ : Type) → Txn σ s ε ρ`, rank-2 so `Current` rows cannot escape). The meanings are `Read.denote` and `Txn.denote`. An abort restores the state and answers `ToProblem ε`.
- `DbHandler`: the program a request runs, typed by its effect (`DbProg s e`: a `Read` for reads, a `Txn` whose abort value is the response for writes). Its law `prog_denote` says the program's meaning is the handler's meaning, **both response and next state**. It is derived over `Path`, pure inputs (`FromRequest.Pure`) and `Auth`. `Txn.mapErr` with `denote_go_mapErr` turns `ε` into a response.
- `AuthenticatesDb.sessions`/`passwords` are read programs, and `Authenticates (DbState s)` is defined as their denotation. So authentication runs inside the request's snapshot or transaction.
- `DbEndpoint`/`DbApi` (`get`/`head`/`post`/`put`/`patch`/`delete`), `dbapi!`, and `DbApi.service` over `DbConns` (one writer, read-only readers, each connection on its own thread). Reads use `Read.run`, which is one snapshot. Writes use `Txn.run`: `BEGIN IMMEDIATE`, with a SAVEPOINT per write.
- Faults: 503 plus `retry-after` for locking or a full queue, 500 otherwise. Faults are logged as `db_fault` with the request id, and the body carries no detail.

Acceptance, on the test schema (`tests/Tests/DbEndpoint.lean`: two entities with a unique index and a reference, plus sessions):
- A `Read` endpoint and a `Txn` endpoint (`join`) answer correctly over HTTP.
- `api_step_safe`, `api_inductive` (with `join`'s preservation obligation) and `getMember_isolated` (via `Api.noninterference`) are proved, with no `sorry`, and pass the axiom audit.
- `dbapi!` checks arity (pinned with `#guard_msgs`), and `describe` prints the `Read …`/`Tx …` signatures.
- A `GET` returning a `Tx` does not compile (pinned).
- Tests: abort discards the insert (`team full` → 409, name not taken afterwards), duplicate → 409, run = denote for reads and for a committed write, one snapshot for count and page, revocation seen by the next request, a locked writer → 503 with nothing written, a poisoned reader → 500.

**Finding for LeanDB (blocks LAPI-06/07, not this ticket).** At `d33d067` (still true after M14b), `DbState.get`/`set`/`source`/`load` are `@[implemented_by]`, and their proof-side bodies ignore the state (`get` is always the empty table, `set` returns the state unchanged). So in proofs every `DbState` is empty, `Read.denote p st` does not depend on `st`, and any isolation claim holds trivially (checked by `rfl` with no view hypothesis). The laws above have the right form and will mean something once `DbState` has a real proof-side model. M15 must replace the `unsafeCast` slots with a dependent map, e.g. `(t : Table) → Table (pack t).ty`.
