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

## 3. The interface

**The design rule:** an operation's type says exactly what it answers and exactly how it can fail. There is nothing else to handle, and nothing in the type that cannot happen.

- **Reads answer `Option` or the value.** On a well-formed database they cannot fail, so they have no error channel at all.
- **Every write has its own failure type,** derived from the schema: which unique index clashed, which reference is missing, who still references the row, and the current row when a compare-and-swap loses.
- **Failures that can't happen are absent from the type.** A table without unique indexes has no `duplicate` failure. Invalid values can't reach a write, because writes take checked values. A row read inside the same transaction can't be stale.
- **Infrastructure faults are not failures of the program.** A lock timeout, an I/O error or a corrupt file is outside every program's type (§3.8).

The sketches give shape, not final names.

### 3.1 Declaring a schema: the failures come from it

```lean
structure User where
  name  : UserName
  email : Email
  team  : Ref Team
  deriving LeanDb.Entity

unique User.byName  := name
unique User.byEmail := email
```

From these declarations LeanDB generates typed symbols. Today unique indexes are string lists (`IndexSpec`); they become declarations.

| Generated | Meaning | For `User` |
|---|---|---|
| `Unique User` | one constructor per unique index | `byName`, `byEmail` |
| `Unique.Key : Unique α → Type` | the key's type, computed from the index | `byName ↦ UserName`, `byEmail ↦ Email` |
| `ForeignKey User` | one constructor per `Ref` field, with its target entity | `team` (target `Team`) |
| `ListField User` | one constructor per child list | (none) |
| `ReferencedBy s User` | every foreign key in schema `s` that points at `User` | e.g. `Membership.user` |
| `Checked User` | a `User` that satisfies its invariant: `{u : User // User.Invariant u}` | built by `User.check` |

`Field α` (typed column symbols) already exists; it types filters and ordering keys.

### 3.2 Reads: answer the value or `none`, never fail

| Operation | Type | Answers |
|---|---|---|
| `get id` | `Read s (Option (Stored α))` | the row with that id, or `none` |
| `lookup ix key` | `Read s (Option (Stored α))`, where `key : ix.Key` | the row holding that unique key, or `none` |
| `first q` | `Read s (Option (Stored α))` | the first row in the query's order, or `none` |
| `all q` | `Read s (List (Stored α))` | every matching row, in order |
| `page q p` | `Read s (Page (Stored α))` | one page and the total, from the same snapshot |
| `count q` | `Read s Nat` | how many rows match |
| `exists q` | `Read s Bool` | whether any row matches |

A **query** is typed by the rows it returns:

```lean
def openTickets (me : Id User) : Query s Ticket :=
  .from Ticket |>.where (·.assignee == some me && ·.status == .open) |>.orderBy (.desc .created)

def withTeam (q : Query s User) : Query s (Stored User × Stored Team) :=
  q.join .team          -- follows the `team` foreign key; the result type says so
```

- `where` takes a Lean predicate over the row. It is elaborated to a `Pred` and refused when it cannot be planned exactly, so what SQL filters is what the predicate says.
- `orderBy` takes typed field symbols (`.created : Field Ticket`), and every order ends with the id.
- `join` follows a declared foreign key, so the pair type in the result is determined by the schema.

### 3.3 Writes: each with its own success value and its own failures

| Operation | Type | Use it when |
|---|---|---|
| `insert v` | `Txn s ε (Except (InsertError α) (Stored α))` | creating a row |
| `update old new` | `Txn s ε (Except (UpdateError α) (Stored α))` | changing a row read *before* this transaction (the client sent its revision): compare-and-swap |
| `set row new` | `Txn s ε (Except (SetError α .all) (Current α))` | replacing a row read *in* this transaction |
| `patch row { f := v, … }` | `Txn s ε (Except (SetError α fs) (Current α))`, where `fs` is the set of fields written | changing some fields of a row read in this transaction |
| `append old new` | `Txn s ε (Except (AppendError α) (Stored α))` | growing child lists (a move log) |
| `delete id` | `Txn s ε (Except (DeleteError s α) (Stored α))` | removing a row; answers the deleted row |

`v` and `new` are `Checked α`, so an invariant can never fail at a write. A `Checked α` is built one of two ways:
- at runtime, by `α.check v : Except (InvalidFields α) (Checked α)`, a domain failure that names the failing fields;
- from a proof, by `Checked.of v h`, when the domain has already proved the invariant (for example with `preserves`). No check runs.

The failure types:

```lean
inductive InsertError (α) [Entity α] where
  | duplicate (ix : Unique α) (holder : Id α)   -- the row that already holds that key
  | missingRef (fk : ForeignKey α)              -- the referenced row does not exist

inductive UpdateError (α) [Entity α] where
  | stale (current : Stored α)                  -- changed since `old`; here is what it is now
  | gone                                        -- deleted since `old`
  | duplicate (ix : Unique α) (holder : Id α)
  | missingRef (fk : ForeignKey α)

/-- Failures of writing the fields `fs` of a row read in this transaction.
    No `stale`: nothing else can change the row before the transaction ends. -/
inductive SetError (α) [Entity α] (fs : Fields α) where
  | gone                                                          -- this transaction deleted it
  | duplicate (ix : Unique.Touching fs) (holder : Id α)           -- only indexes over written fields
  | missingRef (fk : ForeignKey.Within fs)                        -- only references among written fields

inductive AppendError (α) [Entity α] where
  | stale (current : Stored α)
  | gone
  | notAppend (list : ListField α)              -- that list would shrink or change, not grow

inductive DeleteError (s) (α) [Entity α] where
  | gone
  | restricted (by : ReferencedBy s α) (rows : Nat)   -- still referenced, by these rows
```

Every constructor carries what the caller needs: the holder of a clashing key (for a `409` with a `Location`), the current row of a lost compare-and-swap (for a `412` with the current `ETag`), which reference is missing, who blocks a delete.

**The failures of a write depend on what it writes.** `patch` records the written fields in its type (`fs`, computed from the `{ f := v, … }` literal). `Unique.Touching fs` has a constructor only for unique indexes over a written field, and `ForeignKey.Within fs` only for references among the written fields. Writing a game's `moves` and `rev` can't clash on a unique key or break a reference, and its type says so. Writing `resigned := some p` can break a reference, and its type says that too.

**Absent failures are absent types.**
- If `α` declares no unique index, `Unique α` has no constructors, so `duplicate` cannot be built and a `match` need not mention it (Lean checks this). The same holds for `missingRef` with no `Ref` fields, `notAppend` with no child lists, and `restricted` when nothing references `α`.
- When a failure type is empty altogether, `insertNew v : Txn s ε (Stored α)` needs no handling. It requires `[IsEmpty (InsertError α)]`, which is found automatically.

**Schema changes surface at every write site.** Adding `unique User.byEmail` adds a constructor to `Unique User`. Every exhaustive `match` on `InsertError User` then stops compiling until the new failure is handled. A new constraint cannot be silently forgotten in some handler.

### 3.4 Rows read in this transaction

Inside a `Txn`, reads answer `Current α` rather than `Stored α`. A `Current α` is a row this transaction has seen. Since a transaction is serializable, nothing else can change the row before it ends. That is why `set` and `patch` (on a `Current α`) have no `stale`, while `update` (on a `Stored α` from outside) does.

- `Current α` coerces to `Stored α`.
- It cannot leave its transaction. `Txn` is indexed by a transaction variable, and `Txn.run` takes a program that works for every such variable, as the `ST` monad does. So a `Current α` from one request cannot reach the next one.
- **The one failure types cannot rule out is `gone`.** If this transaction deleted the row, a later write through its handle answers `gone`. Ruling that out statically would need linear types (a handle consumed by `delete`), which Lean does not have. So `SetError` keeps `gone`, and it arises in exactly that case. A program that never deletes the row handles it in one line.

### 3.5 Programs: failures are declared

```lean
Read s α        -- reads only; one snapshot; total on a well-formed database
Txn s ε α       -- reads and writes; may abort with ε; all or nothing
```

- `Read s α` embeds into `Txn s ε α`.
- `throw (e : ε) : Txn s ε α` aborts, discarding every write of the transaction.
- `op.orAbort f`, with `f : E → ε`, turns an operation's failure into the program's. Because `f` is a function on `E`, handling is exhaustive by construction.
- `op.orElse g` recovers instead (for example, on `duplicate`, return the existing holder).

The program's declared `ε` is its failure type. At the API it is the endpoint's failure type, with `ToProblem ε` giving each constructor a typed 4xx/5xx status.

### 3.6 Examples

**Register: a clash on the name becomes a typed domain failure.**

```lean
def register (u : Body Register) : Txn Accounts RegisterError (Created UserView) := do
  let row ← insert (← User.check u.val |>.orAbort .invalid) |>.orAbort fun
    | .duplicate .byName _ => .nameTaken
  return ⟨UserView.of row⟩
```

`User` has one unique index and no references, so the `match` above is exhaustive. Add `unique User.byEmail`, and this line stops compiling until an `.emailTaken` is chosen.

**Read a game: `none` is the only non-answer.**

```lean
def readGame (me : Auth PlayerId) (id : Path GameId) : Read Games (Except GameError (Versioned GameView)) := do
  match ← first (Game.visibleTo me.val |>.where (·.id == id.val)) with
  | some g => return .ok g.versioned
  | none   => return .error .hidden
```

**Play a move: the only stale case is the one the client can cause.**

```lean
def playMove (me : Auth PlayerId) (rev : IfMatchRequired Revision) (mv : Body MoveBody) (id : Path GameId) :
    Txn Games GameError (Versioned GameView) := do
  let some g ← first (Game.visibleTo me.val |>.where (·.id == id.val)) | throw .hidden
  let g' ← PrivateGames.playMove me.val rev.val mv.val.cell g.val |>.orAbort .domain
  let row ← patch g { moves := g'.moves, rev := g'.rev } |>.orAbort fun
    | .gone => .hidden      -- only if this program had deleted `g`; it didn't, but the type can't know
  return row.versioned
```

- The client's revision is checked by the domain: `playMove` refuses a stale revision with its own typed failure.
- The database write is a `patch` on a row read in this transaction. It writes `moves` and `rev`, which no unique index covers and which are not references. So the only failure left in its type is `gone`.
- The new values need no runtime check. `Valid.preserved_playMove` already proves that `g'` satisfies `Game`'s invariant, so the `Checked` evidence comes from the proof (`Checked.of`) rather than from `Game.check`.

**Delete a note: who blocks it is in the type.**

```lean
def deleteNote (me : Auth User) (id : Path NoteId) : Txn Notes NoteError NoContent := do
  let some n ← first (Note.ownedBy me.val |>.where (·.id == id.val)) | throw .notFound
  let _ ← delete n.id |>.orAbort fun
    | .gone => .notFound
    | .restricted (.comment) k => .hasComments k
  return {}
```

### 3.7 Meaning

- `Read.denote : Read s α → DbState s → α`. It is total, and needs no error type, on a well-formed state.
- `Txn.denote : Txn s ε α → DbState s → Except ε α × DbState s`. An abort returns the original state.
- **Each failure constructor is produced exactly when its condition holds in the meaning.** For example, `insert` answers `.duplicate ix h` exactly when the row `h` already holds `ix.keyOf v`. This is a law, stated per constructor, and it is what makes the error types trustworthy: a handler's `match` covers exactly the situations that occur.
- Where several failures apply, the meaning fixes which is reported (index declaration order, then foreign keys in field order), and execution reports the same one. Execution checks constraints explicitly and in that order, inside the transaction, rather than relying on which constraint SQLite happens to trip first.

### 3.8 Faults are not failures

Execution can also stop for reasons outside the program: the database is locked beyond the timeout, an I/O error, a corrupt file, a schema mismatch found at startup, a poisoned connection. These are `DbFault`s.

- They are not part of `Read` or `Txn` types, because the meaning never produces them.
- A fault aborts the whole request with no effect (it is one transaction), and the runtime answers `503`.
- The trusted step is stated accordingly: *if execution completes, its result and new state are the meaning's.*
- A row that fails to decode would also be a fault. On a well-formed state it cannot happen (§3.9), so if it ever does, it signals a broken assumption (a raw-SQL edit, a bad migration), and the runtime logs it loudly.

### 3.9 Database state and well-formedness

```lean
/-- A table's contents: the AUTOINCREMENT counter, and rows by id (in id order). -/
structure Table (α : Type) [Entity α] where
  next : Nat
  rows : List (Stored α)            -- sorted by id; ids < next; child lists attached

/-- The whole database, one table per entity of the schema. -/
structure DbState (s : Schema) where
  tables : (t : s.Tables) → Table t.ty

/-- Every row decodes and is `Checked`, and every constraint holds:
    unique keys, references, enum checks. -/
def DbState.WF (st : DbState s) : Prop
```

Production state is abstracted to `DbState` by reading every table in id order, which is `fetchAll`'s order. Every write preserves `WF` (a law, §3.10). An empty database is well-formed, and a migration must establish it. So `WF` is an invariant of every reachable state, which is what makes reads total and decode failures impossible.

### 3.10 Compilation

- **Reads.** WHERE is `render pred.approx`; ORDER BY is the keys, then the ids. LIMIT/OFFSET and COUNT/EXISTS are pushed into SQL only when the plan is exact (`approx = pred`); otherwise they run in Lean after the filter. `lookup ix key` uses the unique index.
- **Writes.** Constraints are checked explicitly, in the meaning's order, inside the transaction: `lookup` for each unique index, an existence check for each reference, a count per referencing key for `delete`. Then the statement runs, so the reported failure is the meaning's. `update` is a compare-and-swap on the parent columns (`IS` semantics); on no match, a `get` distinguishes `stale current` from `gone`.
- **Programs.** A `Read` runs in one deferred transaction on a reader connection. A `Txn` runs under `BEGIN IMMEDIATE`, with a SAVEPOINT around each write so a failed write that the program recovers from (`orElse`) leaves nothing behind. An abort rolls back everything.

### 3.11 Laws: proved once, in LeanDB

| Law | Statement | Status now |
|---|---|---|
| Pushdown | `approx` accepts every row `pred` accepts | proved (`approx_sound`) |
| Exact plans | no opaque leaf ⇒ `approx = pred` | to prove; makes pushed windows and counts sound |
| Aggregates | `count = size ∘ rows`, `exists = !isEmpty ∘ rows`, `first = head? ∘ rows` | to prove, by definition of the meaning |
| Codecs | `fromCol (toCol v) = .ok v`; order preservation for `LawfulSqlOrd` | to add as fields of `ColCodec`/`SqlOrd`; bound or remove `SqlOrd Nat` |
| Frame (reads) | a query's meaning depends only on the tables in its footprint | to prove |
| Frame (writes) | a write changes only its own table, its children, and cascades | to prove |
| Well-formedness | every write that succeeds preserves `WF` | to prove; makes reads total and decode failures unreachable |
| Failure exactness | each failure constructor is produced exactly when its condition holds (`insert` answers `.duplicate ix h` iff `h` holds `ix.keyOf v`; `update` answers `.stale c` iff the row exists and differs from `old`, with `c` the current row; …), and the reported one is the first in the declared order | to prove, per constructor |
| Write algebra | fresh ids; compare-and-swap succeeds iff the row equals `old`; `get` after `insert`/`delete`; `set` on a `Current` row never `stale` | to prove |
| Programs | `run p = denote p` by induction, from the per-operation fact below | to prove |

**Trusted, and differential-tested once in LeanDB:**
- On a well-formed state, each operation's execution, when it completes, equals its meaning: the same answer, the same failure constructor with the same payload, the same new state. Random `DbState`s and random reads and writes are run against SQLite and against `denote`, and compared. This replaces every per-app differential test.
- SQLite executes the SQL that `render` produces with standard semantics, and is serializable under one writer.

## 4. Carrying proofs to the API

In LeanAPI, an endpoint's effect becomes a LeanDB program over the app's schema:

```lean
def readGame (me : Auth PlayerId) (id : Path GameId) : Read Games (Except GameError (Versioned GameView))
def playMove (me : Auth PlayerId) (rev : IfMatchRequired Revision) (mv : Body MoveBody) (id : Path GameId) :
    Txn Games GameError (Versioned GameView)
```

- **A `Read` endpoint** answers its `Except ε α` as today: `α` through `ToResponse`, `ε` through `ToProblem`. It cannot write, by type, so `Api.step_safe` holds as now.
- **A `Txn s ε α` endpoint** either commits and answers `α`, or aborts with `ε`, which is answered through `ToProblem ε` with every write discarded. So the endpoint's failure type *is* the program's failure type.
- **LeanAPI gives default `ToProblem` instances for the database failures,** with typed statuses:
  - `InsertError`: `duplicate` is 409 with `Location` of the holder; `missingRef` is 422.
  - `UpdateError`: `stale` is 412 with the current `ETag`; `gone` is 404; `duplicate` is 409.
  - `DeleteError`: `gone` is 404; `restricted` is 409, naming what references the row.

  An endpoint can expose them directly (`Txn s (InsertError User) …`) or map them to its own domain failures with `orAbort`.
- **The pure meaning of an endpoint** is `Env → Req → DbState s → Res × DbState s`, from `denote`. `Api.toSys` is a `Props.Sys` over `DbState`.
- **The `Handler` laws are restated over `denote`,** and every existing API theorem keeps its shape:
  - `Api.step_safe`: `Read` has no write constructor.
  - `Api.inductive_of`: `Preserved I` for a `Txn` means its meaning preserves `I`.
  - `Api.noninterference`: unchanged.
- **Production runs the same value through LeanDB,** in one transaction per request. A `DbFault` aborts the request with no effect and answers 503.
- **The carry-over theorem.** From `run = denote`, which is proved by induction from the per-operation trusted step: when a request completes, the running service's answer and new state are `Api.step`'s, on well-formed states. Well-formedness is itself an invariant, by the well-formedness law. So every API theorem about `Api.toSys` holds of production, relative to LeanDB's trusted step.

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
| Constraint violations | typed per operation and derived from the schema (§3.3); checked explicitly in the declared order, so execution reports the meaning's failure |
| Undecodable rows | excluded by `WF`, which every write preserves and migrations must establish; if one ever appears it is a `DbFault` (§3.8), not a failure in any program type |
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

- **`gamesApi` is written over the LeanDB schema** (`Storage/Schema.lean`) with `Read`/`Txn` programs, as in §3.6. For example, `readGame` becomes one `first` over `GameRow`, scoped by `visibleTo me` and the id.
- **Idempotency becomes an ordinary typed write.** The receipts table declares `unique ReceiptRow.byKey := (actor, op, key)`.
  - **The key is claimed first.** A keyed request inserts its receipt *before* deciding. The insert's `duplicate .byKey held` failure *is* the replay: `held` is the earlier request's receipt, which is replayed, or refused with 422 if the fingerprint differs.
  - **Then it decides, and records.** On a successful claim it decides, then `patch`es the claim with its answer (`status`, `body`). All of this is one transaction, so a refused request rolls back its claim too.
  - **Why not insert at the end?** Inserting the receipt after deciding would detect a clash only after the change was made. The unique index, the failure type and the retry logic are the same thing, and the exhaustive `match` keeps them in step (the blog post shows the code: `keyed`).
- **The theorems carry over.** GET safety, `api_allValid`, `api_uniqueIds` and `api_noninterference` are re-established on `DbState`; `Model.World` becomes redundant.
- **Deleted:**
  - `Model/` (after its remaining theorems move: keyed replay, `movesGrow`, trace isolation);
  - `App/Service.lean` and the hand-written `Storage/Repo.lean`;
  - the app-level differential test.

  The app keeps one end-to-end HTTP test; LeanDB owns the execution-equals-meaning test.

The staging is in [PLAN.md](../PLAN.md), milestones M13–M16; the LeanAPI tasks are [LAPI-01…09](../tickets/README.md).
