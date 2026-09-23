# Queries and transactions as values: carrying proofs from LeanDB to the API

Status: design, 2026-09-23. Extends [DESIGN.md §7.4](../DESIGN.md). Based on a study of LeanDB 0.4.0 (pinned by LeanAPI) and mainline (LDB-15, LDB-16); file references are to `LeanDb/` in the pinned checkout unless marked *mainline*.

## Why

The whole point: a property proved about the API should be a property of the running service, including its database. Today it is not:

- `gamesApi` is proved correct, but it runs over an in-memory `World`.
- The production service is a second implementation over LeanDB (`App/Service.lean`, `Storage/Repo.lean`). Its equivalence to `gamesApi` is only checked, by a differential test.
- Nothing proved about queries in LeanDB carries up to the API either. The two layers meet in hand-written `DbM` code that neither side's proofs cover.

The goal is **one definition** of each endpoint that:
- has a pure meaning, which the API proofs are about;
- runs against LeanDB in production;
- is connected to production by a single, engine-level trusted step: *executing a value equals its meaning*, checked once in LeanDB rather than per application.

That needs LeanDB to offer a **declarative query and transaction language**: queries and writes as data, with a meaning, a SQL compilation, and laws. This document says what exists, what is missing, and what to build.

## 1. What LeanDB offers today

**Reads**

- **`select ts where' sortBy`** (`Db.lean:750`).
  - The `leandb_plan` tactic reifies the Lean lambda into a `Pred ts` (`PlanElab.lean`). It handles comparisons, `&&`/`||`/`!`, `if`, Option tests, EnumSet membership, `any`/`all` over child lists and closed enums. Anything else becomes an `opaque` leaf.
  - The pushable part, `approx`, goes to SQL, and the lambda is re-applied in Lean to what comes back.
- **`selectP ts p sortBy order window`** (`Db.lean:777`) takes the plan as data. `countP`/`existsP` push `COUNT(*)`/`EXISTS` for single tables (`:1143`, `:1161`).
- **The reference meaning is `selectSpec`** (`Select.lean:153`): gather rows from any `Source m`, filter with the predicate, sort with an id tiebreak. `Pred.denote` (`Pred.lean:413`) gives each plan a Lean meaning.
  - Because `selectSpec` is generic over the monad and the source, the same query has a pure meaning over in-memory tables.
- **`Pred` is already a small declarative filter language** (`Pred.lean:220-260`):
  - column/value and column/column comparisons (null-safe, in the encoded domain), and null tests;
  - EnumSet bits, `and`/`or`;
  - `exists`/`forall` over foreign-key children, the only part that needs a `Snapshot`;
  - `opaque` Lean functions.
- **`Footprint`** (`Pred.lean:270`) records the tables and columns a plan's pushed leaves read.

**Proved:** `approx_sound` (`Pred.lean:495`, pushdown never excludes a row the plan accepts), `denote_andS`/`denote_orS`, `any_mono`/`all_mono`, `size_neg`, `Col.nil_elim`. Nothing else.

**Writes:**
- `insert`: `AUTOINCREMENT` ids, returned via `lastInsertRowId`.
- `update old new` (`:532`): a compare-and-swap on the parent's encoded columns. `.stale` or `.notFound` on failure; child lists are replaced, not compared.
- `append` (*mainline* `:609`): lists must grow, with a length check.
- `patch` (`:1195`) and `delete` (`:576`): RESTRICT on references, CASCADE to children.
- Unique and partial indexes, and entity invariants (*mainline*).
- **No write has a pure meaning.**

**Transactions:**
- `transaction` is `BEGIN IMMEDIATE`, with SAVEPOINTs when nested (`Transaction.lean:39`).
- The deferred read snapshot is private (`Db.lean:380`); LeanAPI rebuilt one (`Repo.lean:178`).
- SQLite runs one writer at a time, so `BEGIN IMMEDIATE` read-modify-write is serializable. A deferred read transaction is a consistent snapshot, and reads inside a write transaction see its own writes.

**Everything runs in `DbM`.** `DbM := ReaderT Conn (ExceptT DbError IO)` (`Db.lean:142`), and `untrackedSqlite` hands out the raw handle. **There are no query values:** only the tuple `(ts, Pred, SortBy)` is data, and `select …` is an action. (This corrects DESIGN §7.4, which called `select` a value.)

## 2. What stops proofs from carrying over

Ranked, with concrete failures where they exist.

1. **There is no pure database state and no meaning for writes.** Invariants and idempotence need `write : DbState → DbState`. Today the only pure state is `Pred.Snapshot`, and it drops child lists and silently skips rows it cannot decode (`Pred.lean:197-201`).
2. **Queries and transactions are not values, and there is no read-only type.** A `DbM` function can write, so "GET never writes" cannot be read off a `DbM` type. A type class such as `MonadDbRead` can rule out writes, but cannot prove that running equals the meaning (that would need parametricity). A deep embedding can.
3. **Order, window and counts have no meaning, and compose wrongly.**
   - `Order` is an untyped column name (`Select.lean:53`); `Window` (`:60`) has no meaning.
   - `plannedSource` applies `order`/`window` to table 0's SQL fetch, *before* the residual Lean filter and before the product (`Db.lean:629`). So with an opaque leaf, `existsP` takes `LIMIT 1` first and filters afterwards (`:1164`), and can answer `false` when a matching row exists. Pagination has the same bug.
   - The join path ignores `order`/`window` (`:676`), and a given `order` drops `sortBy` (`:680`).
   - `count`/`exists?` use only the plan, never the lambda (`:1158`, `:1176`).
   - `fetchFiltered` means `approx`, not the plan (`Pred.lean:644`).
4. **Pushdown and codec laws are assumed, and one is false.**
   - `SqlOrd` is an empty class (`Core.lean:220`). The `Nat` codec wraps at 2^63 (`Core.lean:245-254`), so `select (·.n < 2^64)` pushes `n < 0` and returns no rows, where the meaning returns all of them.
   - `ColCodec` has no round-trip law; consumers prove their own (`Schema.lean:30-46`).
5. **Whether a read fails depends on the plan.**
   - One undecodable row fails a whole query. Rows are decoded from the `approx` superset, so the pushed-vs-residual split, `select` vs `selectUnplanned`, and `countP` (which decodes nothing) can disagree about failing.
   - Execution can only equal the meaning on a **well-formed state**: every row decodes and satisfies its invariant.
6. **Atomicity and connection hazards.**
   - A verb inside a transaction joins it without a SAVEPOINT (`Db.lean:387`). If a caller catches an error and commits, partial effects are kept.
   - `Runtime.Service.withReader` hands out connections round-robin with no per-connection lock. With `readers := 0` it hands out the writer connection outside the writer mutex (`Runtime.lean:162-176`).
7. **Footprints cover read filters only.** They are not attached to query values, and writes have none.
8. **No projections or aggregates** beyond count/exists. This is performance only; it doesn't affect meaning.

## 3. The language

All of it is data, in LeanDB. Names reuse what exists (`Pred`, `Footprint`, `Entity`, `Stored`, `Id`, `RowsOf`). The sketches give shape, not a final API.

### 3.1 Database state

```lean
/-- A table's contents: the AUTOINCREMENT counter, and rows by id (in id order). -/
structure Table (α : Type) [Entity α] where
  next : Nat
  rows : List (Stored α)            -- sorted by id; ids < next; child lists attached

/-- The whole database, one table per entity of the schema. -/
structure DbState (schema : Schema) where
  tables : (t : schema.Tables) → Table t.ty

/-- Every row decodes, satisfies its invariant, and every constraint of the
    schema holds (unique indexes, foreign keys, enum checks). -/
def DbState.WF (s : DbState schema) : Prop
```

Production state is abstracted to `DbState` by reading every table in id order, which is `fetchAll`'s order. Everything below is defined on `DbState`.

### 3.2 Queries

```lean
/-- A total order: typed keys, then ids (so results are deterministic). -/
inductive Key (ts : List Type) where
  | asc  {τ} [LawfulSqlOrd τ] (c : Pred.Col ts τ)
  | desc {τ} [LawfulSqlOrd τ] (c : Pred.Col ts τ)

structure Query (ts : List Type) where
  pred : Pred ts
  order : List (Key ts) := []
  window : Window := {}             -- offset, limit

/-- What a query answers. -/
inductive Agg (ts : List Type) : Type → Type 1 where
  | rows : Agg ts (Array (Rows ts))
  | count : Agg ts Nat
  | exists : Agg ts Bool
  | first : Agg ts (Option (Rows ts))
```

**Meaning:** `window (sortBy keys-then-ids (filter pred.denote (gather s)))`, followed by the aggregate (`id`, `size`, `!isEmpty`, `head?`). This is `selectSpec` with order, window and aggregate added, and it reuses `finishRows`.

**Compilation:**
- WHERE is `render pred.approx`; ORDER BY is the keys, then the ids.
- **LIMIT/OFFSET and COUNT/EXISTS are pushed into SQL only when the plan has no residual**, and the query is a single table or a pushed join. Otherwise they run in Lean after the filter. This fixes gap 3 by construction.
- The query *is* its `Pred`, as in `selectP`, so a plan can no longer disagree with a lambda. The lambda form becomes surface syntax elaborated into a `Query`, rejected if it cannot be planned exactly (no silent `opaque` in positions that would change the meaning of a pushed window or count).

### 3.3 Writes

```lean
inductive WriteOp : Type → Type 1 where
  | insert [Entity α] (v : α) : WriteOp (Id α)
  | update [Entity α] (old : Stored α) (new : α) : WriteOp Unit         -- CAS on old's parent columns
  | append [Entity α] (old : Stored α) (new : α) : WriteOp Unit         -- lists only grow
  | patch  [Entity α] (id : Id α) (sets : Patch α) (guard : Pred [α]) : WriteOp PatchResult
  | delete [Entity α] (id : Id α) : WriteOp Unit
```

**Meaning:** `WriteOp.denote : DbState → Except DbError (β × DbState)`. It models what SQLite and LeanDB do:
- `insert` assigns `next` and increments it; ids are never reused.
- `update` and `append` fail with `.stale` unless the stored parent columns equal `old`'s, using `IS` semantics.
- A unique-index clash is `.duplicate`, a missing reference is `.missingRef`, and deleting a referenced row is `.restricted`. Child rows cascade.
- A failed invariant or enum check is an error, not a stored row.
- When several constraints fail, the error LeanDB reports first is the one the meaning reports.

### 3.4 Programs: read-only by type

```lean
inductive Prog (Op : Type → Type 1) (α : Type) where
  | pure (a : α)
  | bind (op : Op β) (k : β → Prog Op α)
  | abort (e : DbError)

inductive ReadOp : Type → Type 1 where
  | query [RowsOf ts] (q : Query ts) (a : Agg ts β) : ReadOp β
  | get [Entity α] (id : Id α) : ReadOp (Option (Stored α))

abbrev Reads := Prog ReadOp                    -- no write constructor exists
abbrev Txn   := Prog (fun β => ReadOp β ⊕ WriteOp β)
```

A later query can depend on an earlier result (`bind`), so this is a free monad, not an applicative plan. `Reads` has no way to write, so read-only is a property of the type, which is what `Api.step_safe` needs.

**Meaning:** `Reads.denote : DbState → Except DbError α` and `Txn.denote : DbState → Except DbError (α × DbState)`. They run in sequence, reads see earlier writes, and an `abort` or error discards every write: all or nothing.

**Execution:**
- A `Reads` program runs in one deferred read transaction on a reader connection, so it sees one snapshot.
- A `Txn` runs under `BEGIN IMMEDIATE`, with a SAVEPOINT around each write. A failed write rolls back to its SAVEPOINT; an abort rolls back the transaction.

### 3.5 Laws: proved once, in LeanDB

| Law | Statement | Status now |
|---|---|---|
| Pushdown | `approx` accepts every row `pred` accepts | proved (`approx_sound`) |
| Exact plans | no opaque leaf ⇒ `approx = pred` | to prove; makes pushed windows and counts sound |
| Aggregates | `count = size ∘ rows`, `exists = !isEmpty ∘ rows`, `first = head? ∘ rows` | to prove, by definition of the meaning |
| Codecs | `fromCol (toCol v) = .ok v`; order preservation for `LawfulSqlOrd` | to add as fields of `ColCodec`/`SqlOrd`; bound or remove `SqlOrd Nat` |
| Frame (reads) | a query's meaning depends only on the tables in its footprint | to prove |
| Frame (writes) | a write changes only its own table, its children, and cascades | to prove |
| Well-formedness | every `WriteOp` that succeeds preserves `WF` | to prove; makes decode and invariant failures unreachable |
| Write algebra | fresh ids; CAS succeeds iff the row equals `old`; `get` after `delete` is `none`; … | to prove |
| Programs | `run p = denote p` by induction, from the per-operation fact below | to prove |

**Trusted, and differential-tested once in LeanDB:**
- On a well-formed state, each operation's execution equals its meaning. Random `DbState`s and random `Query`/`WriteOp` values are run against SQLite and against `denote`, and compared. This replaces every per-app differential test.
- SQLite executes the SQL that `render` produces with standard semantics, and is serializable under one writer.

## 4. Carrying proofs to the API

In LeanAPI, `Reads` and `Writes` become the LeanDB program types:

```lean
-- LeanApi.Http.Endpoint, over a LeanDB schema instead of an in-memory σ
def Reads (schema) (α) := LeanDb.Reads α
def Writes (schema) (α) := LeanDb.Txn α
```

- **The pure meaning of an endpoint** is `Env → Req → DbState schema → Res × DbState schema`, using `denote`. `Api.toSys` is a `Props.Sys` over `DbState`.
- **The `Handler` laws are restated over `denote`.** Every existing API theorem keeps its shape: `Api.step_safe` (no write constructor), `Api.inductive_of` (`Preserved I` for a `Txn` means its meaning preserves `I`), and `Api.noninterference`.
- **Production runs the same value through LeanDB**, in one transaction per request.
- **The carry-over theorem:** by `run = denote` (proved by induction from the per-operation trusted step), every API theorem about `Api.toSys` holds of the running service, for requests that reach the handler, on well-formed states. Well-formedness is itself an invariant, by the write-algebra law.

**Isolation gets two things from values:**
- **Cheaper proofs.** Frame lemmas mean a query whose predicate is scoped to `p` (it implies `visible p`) returns the same rows in any two states that agree on `p`'s rows. `SameView` can then be *defined* from the scoped queries rather than written by hand.
- **A stronger property, restricted logical reads.** Every query issued on behalf of `p` has a predicate implying `visible p`, so other players' rows are never fetched (DESIGN §6.3). This is a statement about the `Pred` values in the program, and much of it can be checked mechanically.

## 5. Database behaviour the meaning must get right

| Concern | How it is handled |
|---|---|
| Id assignment | the per-table AUTOINCREMENT counter is part of `DbState`; ids are never reused, as in SQLite |
| Row order | id order is the base order; every order ends with the id tiebreak; `.preserve` means id order |
| Pagination and counts | pushed only for exact plans; otherwise computed in Lean after the filter |
| Snapshots | one transaction per request: deferred for `Reads`, `BEGIN IMMEDIATE` for `Txn` |
| Own writes | reads inside a `Txn` see its earlier writes, in the meaning and in SQLite |
| Partial failure | a SAVEPOINT around each write; all-or-nothing per request |
| Concurrency | one writer (SQLite plus the runtime's single writer), so executions are serializable; the pure meaning is sequential |
| Constraint violations | modeled in `WriteOp.denote` with the error LeanDB reports |
| Undecodable rows | excluded by `WF`, and `WF` is preserved by every write; migrations must establish it |
| Numeric range | codecs carry their range; `Nat` columns are bounded (or `SqlOrd Nat` is removed) |
| Connections | a public read snapshot; readers locked per connection; no writer connection handed out as a reader |
| Migrations | a migration is a function `DbState s → DbState s'` that must establish `WF` and carry declared invariants (later) |

## 6. Fix now, whatever else happens

These LeanDB bugs are independent of the new language:

1. **Window before filter** (`Db.lean:629`, `:1164`, `:1168`). `existsP` and pagination can miss matching rows. Apply the window after the residual filter unless the plan is exact.
2. **`SqlOrd Nat` is unsound** above 2^63 (`Core.lean:245-254`).
3. **`Runtime.Service.withReader`** hands out the writer connection with `readers := 0`, and does not lock readers (`Runtime.lean:162-176`).
4. **Nested verbs are not atomic** (`Db.lean:387`). Wrap multi-statement verbs in a SAVEPOINT when joining an outer transaction.
5. **`patch`'s guard** renders an opaque leaf as true (`Db.lean:1195`). Reject opaque guards.
6. **`count`/`exists?`** ignore the lambda's residual (`Db.lean:1158`, `:1176`).
7. **`Snapshot.rows`** silently drops undecodable rows (`Pred.lean:197-201`). Fail as the executor does.

## 7. What changes in private-games

- **`gamesApi` is written over the LeanDB schema** (`Storage/Schema.lean`) with `Reads`/`Txn` values. For example, `readGame` becomes one `Query [GameRow]` with `pred := visiblePred me ∧ id = gid`.
- **The theorems carry over.** GET safety, `api_allValid`, `api_uniqueIds` and `api_noninterference` are re-established on `DbState`; `Model.World` becomes redundant.
- **Deleted:**
  - `Model/` (after its remaining theorems move: keyed replay, `movesGrow`, trace isolation);
  - `App/Service.lean` and the hand-written `Storage/Repo.lean`;
  - the app-level differential test.

  The app keeps one end-to-end HTTP test; LeanDB owns the execution-equals-meaning test.

The staging is in [PLAN.md](../PLAN.md), milestones M13–M16.
