# Review of LeanDB M13 (LDB-17 … LDB-24) at bdd0e4c

Date: 2026-09-23. Scope: the eight M13 commits on LeanDB branch `ldb-m13-fixes` (`61f9bab..bdd0e4c`), against the fixes planned in [QUERIES.md §6](../QUERIES.md) and [PLAN.md M13](../../PLAN.md). Line numbers refer to `bdd0e4c`. The uncommitted M14 work on `ldb-m14-typed` was not reviewed.

## Summary

- LeanDB builds and its whole suite passes ("all engine tests passed").
- LeanAPI, built against this LeanDB, passes everything: 286 tests (including the three-way differential test with the native service on the new LeanDB), the axiom audit (148 theorems), the README snippets and the evidence check. That needs **one proof change**: LDB-18 changed the `Nat` encoder, so `nat_roundtrip` in `Storage/Schema.lean` must first prove `natToSql n = some (Int64.ofNat n)`. The change is prepared and checked in a scratch copy; it lands when LeanAPI moves its pin.
- **But several fixes are incomplete, and LDB-19 introduces regressions.** M13 should not be released as is.

Each finding was reproduced by a scratch script against the committed tip, or confirmed by reading the code.

## High

### R1. LDB-19: after `restore`, readers keep reading the old file (regression)

`Runtime.lean:117-124`, `:204-224`. Reader connections are opened once, in `new`; `restore` reopens only the writer (`conn`).
- Before LDB-19, the default `readers := 0` read through the writer connection, which `restore` reopens, so the default setup was correct. Now every setup is affected.
- Scenario: insert "a", snapshot, insert "b", restore the snapshot, insert "c". The writer sees `[a, c]`; readers see `[a, b]`, permanently.
- Related: `drain` does not wait for readers in the middle of a call, so a restore can swap the file under a live reader.

**Fix:** reopen the reader pool in `restore` (under the per-reader locks), and make `drain` wait for in-flight readers.

### R2. LDB-19: two new deadlocks

- **Nested `withReader` on one thread** (`Runtime.lean:180`). `Std.Mutex` is not re-entrant; re-locking on the same thread is undefined. With the default pool of one reader, a `withReader` inside a `withReader` hangs forever. With N readers it hangs whenever round-robin returns a slot the thread already holds.
- **Lock-order inversion.** Thread B holds a reader lock and calls `withConnection`; thread A holds the writer mutex and calls `withReader`, waiting for B's reader lock. Both hang.

Both completed (unsafely) before this commit. **Fix:** detect re-entrancy as `withConnection` does (`.reentrant`), and never take the writer mutex while holding a reader lock (pick the reader outside the writer's slot; the reader array never changes after `new`, apart from `restore`).

### R3. LDB-17: multi-table plans still push the window into table 0, before the product

`Db.lean:802` (`pushWindow := exact && !hasJoin`) with `plannedSource` (`:749`). "Exact" is not enough: without a join, the rows are a product built in Lean, and the window must apply to the product.
- `Pred [A, B]` = `A.x = 1 ∨ B.y = 2`, with A rows x=0 and x=1 and B rows y=0 and y=5: `existsP` answers **false**; the answer is true. `selectP … limit 1` answers `[]`.
- `A.x ≥ 0 ∧ B.y ≥ 0` with `limit 1` answers **2 rows**; `offset 1` skips A rows, not product rows.

**Fix:** push the window only for single-table plans, or into the joined SQL for pushed joins; otherwise apply it in Lean after the product and the filter.

### R4. LDB-18: comparisons between two constants now fold wrongly (regression)

`Pred.vvEq`/`vvOrd` (`Pred.lean:372-382`) compare two constants through `toCol`, which now clamps at `Int64.maxValue` (`Core.lean:273`). So any two Nats at or above 2^63−1 compare equal.
- `select [Num] (fun r => lo < hi || r.val.n == 5)` with `lo = 2^63`, `hi = 2^63 + 1` answers **0 of 2 rows**; `count` answers 0. The old wrapping happened to get this pair right.
- `vvEq (2^63 − 1) (2^64)` folds to `tt`.

**Fix:** compare constants in Lean (or through `toSql?`, falling back to Lean when it is `none`), never through the clamped encoding.

### R5. LDB-18: some writes still store out-of-range values, now silently clamped

`checkSqlRange` covers only the parent entity's fields on `insert`, `update`, `append` and `insertMany`. Not covered:
- **Child-list rows:** `insertChildRows` (`Db.lean:510`), used by `insert`, `update` and `append`.
- **`patch`** with `Assignment.of` (`Db.lean:1318`): answers `.updated` and stores 9223372036854775807.
- **Hand-written codecs** that do not use `via` inherit the default `toSql? := some (toCol a)` (`Core.lean:227`). Their values are never refused, and a comparison bound such as `q < 2^64` renders as `< 9223372036854775807`, so `selectP` answers 0 rows where the meaning is every row.

The underlying problem is that `toCol` clamps instead of refusing. **Fix:** make range failure impossible to ignore. Either `toCol` returns `Option`/`Except` (so every encode path must handle it), or `toSql?` becomes a required field, and every write path, including child rows and `patch`, checks it. Report the refusal as its own error kind: today it is `.decode`, a read-side kind, and the logged plan JSON shows the clamped bound while the SQL runs `1`.

### R6. LDB-23 does not fix the bug it names (and makes it worse)

`Pred.lean:208-213`. `Snapshot.rows` now calls `panic!`, but in compiled Lean a panic prints and returns the default value, an empty array.
- A `forall` over a snapshot with a child row that decodes but fails the predicate answers `false`. The same snapshot with a corrupt column answers **`true`** after printing a PANIC.
- It now drops *every* row of that table, not only the bad one.
- The new public `Snapshot.addRaw` (`:217`) is the first public way to build such a snapshot; the constructor was private to prevent that.
- The regression test checks `rows?` only and never exercises `forall`.

The executor path is safe, because `Pred.snapshot` goes through `fetchAll`, which throws on undecodable rows. **Fix:** make `denote` over a snapshot total and honest: either the snapshot type guarantees decodability (built only from decoded rows; drop `addRaw`), or `denote` returns `Except`.

## Medium

| # | Finding | Where |
|---|---|---|
| M1 | LDB-17: the join path ignores `order` entirely; a join with `order x desc, limit 1` answered (1,1) instead of (2,2). `sortBy` is still dropped whenever `order` is non-empty. So "order keys, then `sortBy`, then id" does not hold | `Db.lean:805`, `:808` |
| M2 | An offset without a limit is a SQLite syntax error on the pushed path (`OFFSET` with no `LIMIT`); `selectP` with no residual and `{offset := 1}` fails | `fetchFiltered` `:729`, `searchP` `:1462` |
| M3 | LDB-21's class of bug remains in `fetchFiltered` and `scan`: an opaque leaf renders as true and no residual is applied. An opaque-false predicate over 3 rows returns 3 from both (while `countP` returns 0). `scan` is public and takes a `Pred`; `vvOrd` produces such leaves for REAL comparisons | `Db.lean:718`, `:1402`, `:1407` |
| M4 | LDB-24: the public `readSnapshot` does not refuse writes on the writer connection. Writes inside it run in a deferred transaction, and after another connection commits, an insert fails at once with `.sqlite "database is locked"` (SQLite refuses to upgrade a stale snapshot, without waiting on the busy timeout). Nested `withTransaction` becomes a SAVEPOINT, so it does not take the write lock up front as documented | `Db.lean` `readSnapshot`; `Transaction.lean` |

**M4 fix:** mark the connection read-only for the duration (so `requireWritable` refuses), or document it. On reader connections it is correct; writes answer `.readOnly`.

## Low

- **LDB-22** changes cost and failure behaviour.
  - `count`/`exists?` now fetch whole rows, attach child lists and check invariants, even for exact plans; `COUNT(*)`/`EXISTS` are gone. They can fail on rows that were counted before.
  - For multi-table plans they no longer run inside one transaction.
  - The CHANGELOG should say this. With M14's exact plans, the SQL `COUNT`/`EXISTS` can return for exact plans.
- **Readers still queue behind the writer.** Picking a reader takes the writer's `RecursiveMutex` (`Runtime.lean:167`); a `withReader` waited 905 ms behind a 1 s `withConnection` callback. This contradicts the docstring ("concurrent readers proceed").
- **`withReader`** skips the gate check, and keeps handing out a poisoned reader.
- **LDB-21's refusal** is `.sqlite`, indistinguishable from an engine failure. It needs its own error kind.
- **LDB-20:**
  - Every nested read now pays SAVEPOINT/RELEASE.
  - If SQLite itself rolls back the whole transaction (a trigger's `RAISE(ROLLBACK)`), `ROLLBACK TO` fails and the connection is poisoned until reopened. That is safe but not recoverable.
  - Stale docs: the `readSnapshot` docstring ("nested calls join the open transaction") and `Transaction.lean:7-8`.
- **`SqlOrd`** is still an empty `Prop` class with no law, and `SqlOrd Nat` is kept. That was acceptable for M13 (behaviour fixed); the law comes in M15.
- The "limit requires a pushed order" check (`Db.lean:915`) is unnecessary on paths where the window is applied in Lean.

## Tests

- LDB-17, 18, 19, 20, 21 and 22's tests would fail on the old code, so they are meaningful, but they cover only single-table cases and the main `Nat` case.
- LDB-20 covers only `patch` with an invariant. It needs update-with-children, `insertMany` and `append` cases.
- LDB-23's test cannot compile on the old code and does not exercise `forall`.
- LDB-24's test mostly checks that the API is public.
- Missing: restore with readers, nested `withReader`, lock order, multi-table windows, joins with `order`, offset without limit, constant folding at the `Nat` boundary, child-row and `patch` range checks.

## Verified correct

- **LDB-17:**
  - `hasOpaque` looks under `and`, `or`, `exists` and `forall`.
  - On a single table with a residual, the window is applied after the filter for `selectP` and `existsP`; with no residual it is pushed with `ORDER BY keys, id`.
  - `Window.apply` behaves like LIMIT/OFFSET, and on the join path the window now applies after filter and sort.
- **LDB-18:**
  - `insert`, `update`, `append` and `insertMany` refuse an out-of-range parent field before any SQL (including `Option Nat` and inline fields).
  - A bound that does not fit renders `<`, `≤` and `IS NOT` as `1` and the others as `0`, and `denote` uses the same rule (`boundHolds`), so `n < 2^64` agrees with its meaning.
  - `UInt32`, `UInt16`, `Id` and `via` newtypes are fine.
- **LDB-19:** the writer is never handed out as a reader; `readers := 0` opens one dedicated read-only, `query_only` reader; the slot lock is released on exceptions. The test fails 19/20 times on the old code.
- **LDB-20:** every multi-statement write goes through `transaction` (insert or update with children, `append`, `insertMany`, `patch` with an invariant). The remaining ones are single statements. Error path is `ROLLBACK TO` then `RELEASE`; savepoint names are unique per level; behaviour with no outer transaction is unchanged; it works on read-only connections.
- **LDB-21:** opaque leaves inside quantifier bodies are caught; the refusal happens before any write.
- **LDB-22:** `count`/`exists?` now respect the lambda, including with `.tt` plans.
- **LDB-24:** `BEGIN DEFERRED` with no outer transaction, rollback on typed errors and host exceptions, SAVEPOINT when nested, works on readers.
- **LeanAPI private-games is unaffected in behaviour.** Its plans are single-table with no opaque leaf, and it uses neither `count`/`exists?` nor `Snapshot`. The differential test agrees on the new LeanDB.

## Recommended order

1. **R1, R2:** LDB-19's regressions (restore with readers, the two deadlocks). These affect every deployment.
2. **R3, M1, M2:** windows and order: single-table-only pushdown, `order` on the join path, `sortBy` with `order`, offset without limit.
3. **R4, R5:** make range failure impossible to ignore (`toCol` stops clamping), fold constants in Lean, check child rows and `patch`, and give the refusal its own error kind.
4. **R6:** an honest, total `denote` over snapshots; drop `addRaw`.
5. **M3, M4**, then the Low items and the missing tests.
6. Then tag a LeanDB release and move LeanAPI's pin, with the `nat_roundtrip` change.
