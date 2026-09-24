# LAPI-12: private-games: no runtime checks where a type can carry the fact

**Repo:** theoriclabs/leanapi · **Area:** `examples/private-games` (`Domain/Values.lean`, `Storage/Schema.lean`, `DbApi.lean`) · **Priority:** P2 · **Size:** S (part 1), S (part 2, after LeanDB)
**Depends on:** part 2 needs LeanDB reads to return invariant evidence (see below). Easier after LAPI-08 (no `Model/` to update). **Enables:** simpler proofs in LAPI-07.

## Problem

`DbApi.lean` checks two facts at runtime that are already established elsewhere, because the types don't carry them:

1. **Player ids fit in a `Ref` (below 2^63).**
   - `PlayerId.make` checks this when a request is decoded (`SmartCtor PlayerId Nat`), and `pid` guarantees it for ids read from rows (`pid_lt`).
   - But `PlayerId` is a bare `Nat`, so `openGame` checks the range twice more: `opp.n ≥ 2^63` (`DbApi.lean:86`) and `if hb : me.val.n < 2^63 ∧ opp.n < 2^63` (`:90`), to obtain the proof `GameRow.checkedOpen` needs.
   - The second check answers `unknownOpponent` when the *caller's* id is out of range: a wrong error, on an unreachable branch.
2. **A stored game satisfies its invariant.**
   - LeanDB refuses, on every read, a row that fails `GameRow.invariant` (LDB-16).
   - But `Read` returns `Stored GameRow`, with no evidence. So `writeStep` re-checks `GameRow.invariant s.val` in a branch commented "unreachable" (`DbApi.lean:116-121`), to obtain the proof `GameRow.checkedStep` needs.

## Proposal

1. **`PlayerId` carries its bound:** `structure PlayerId where n : Nat; lt : n < 2^63`.
   - `PlayerId.make` already checks the bound and now returns the proof.
   - `pid` builds it from `pid_lt`, and `pref`/`pid` become exact inverses (`pid_pref` loses its hypothesis).
   - `Game.Bounded` then holds for every game. `GameRow.checkedOpen` drops its `hp`/`ho` arguments, and both runtime checks in `openGame` go.
   - The existence check (`Read.get PlayerRow`) stays: it is a fact about the database, not about the value.
   - This is the "domain type at most as wide as the external type" rule of docs/BOUNDARIES.md §3.2, applied to ids.
2. **Invariant evidence from reads (asks LeanDB).**
   - LeanDB already refuses rows that fail the invariant when it reads them. The ask is that it return that evidence: rows of an entity with an invariant come back as `Stored` with `Invariant α r.val` (for example, a `CheckedStored α`, or a field on `Stored`).
   - `writeStep` then takes the evidence from the row, and the runtime branch goes.
   - Record the ask in the LeanDB M15 list (see docs/reviews/2026-09-23-review-lapi-02-05-m14.md, M3).

## Acceptance criteria

- `DbApi.lean` has no runtime range check on player ids, and no invariant re-check (after part 2).
- `GameRow.checkedOpen` takes no range hypotheses.
- `pid_pref : pid (pref p) = p` holds without a hypothesis.
- The HTTP tests (both services) and the differential test pass unchanged. Answers are identical, since the removed branches were unreachable.
- The axiom audit and evidence check pass. `PlayerId.make_lt` is replaced by the field, and EVIDENCE.md's row about `Checked` rows is updated.

## Tests

- None new beyond the build: the removed branches were unreachable. A decoding test for an id ≥ 2^63 in a body (422 naming the field) pins that the bound is still enforced at the edge.

## Compatibility

- **Internal to the example.** `PlayerId` is not part of any wire format change: the JSON stays a number, and ids ≥ 2^53 are a separate issue (docs/BOUNDARIES.md A1).
- **`Model/` code that builds ids as `⟨n⟩` needs the bound.** Do part 1 after LAPI-08 retires the model, or supply the proof there.

## Status (2026-09-23): part 1 done; part 2 waits for LeanDB (in progress there)

**Part 1** (done on the M14c pin, *before* LAPI-08: I supplied the proofs in `Model/`):
- `PlayerId` has `lt : n < 2^63 := by decide`. `PlayerId.make` returns the proof, `pid` builds it, and `pid_pref : pid (pref p) = p` needs no hypothesis.
- `Game.bounded` holds for every game. `GameRow.checkedOpen` takes no range arguments, and `openGame` in `DbApi.lean` lost both runtime range checks and the wrong-error branch. The existence check stays.
- The model's witnesses use `PlayerId.next` (a bounded successor, with `next_ne` and `next_next_ne`) instead of `⟨p.n + 1⟩`. Literals use `PlayerId.lit n`, checked by `decide`. Tests use `PlayerId.ofNat!`.
- An opponent id ≥ 2^63 in a body still answers 422 naming `body.opponent` (a new test).
- 432 tests pass (3 runs; the differential test included), the axiom audit passes (168), and EVIDENCE.md is regenerated (the `Checked` row now cites `Game.bounded`, `pid_pref`).

**Part 2** (`writeStep`'s invariant re-check): not done. At the pinned LeanDB `afe4544`, `Read.get`/`first` return `Stored α`, with no evidence. LeanDB's uncommitted working tree (`ldb-m15-state`) already adds `Valid α` (a stored row with `Invariant α r.val`), returns it from `Read.get`/`lookup`, and makes `Current` carry `property`. Once that lands and is pinned, `writeStep` takes the evidence from the row and the `else Txn.throw .hidden` branch goes.
