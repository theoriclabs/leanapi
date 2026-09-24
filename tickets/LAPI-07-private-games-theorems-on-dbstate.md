# LAPI-07: Re-establish private-games' theorems on `DbState`, plus restricted logical reads

**Repo:** theoriclabs/leanapi · **Area:** `examples/private-games/PrivateGames/ApiProofs.lean`, `ApiIsolation.lean` · **Priority:** P1 · **Size:** L
**Depends on:** LAPI-05, LAPI-06, LeanDB M15 (frame lemmas, failure-exactness laws). **Enables:** LAPI-08.

## Problem

These theorems are proved about the in-memory typed API (`gamesApi` over `Model.World`):
- `api_reads_safe`;
- `api_allValid`, `api_uniqueIds`, `api_freshIds`;
- `api_noninterference`, `api_existence_private`.

After LAPI-05, `gamesApi` is over `DbState Games`, so they must be proved again there. By LAPI-06 they then hold of the running service.

## Proposal

- **GET safety:** free from `Api.step_safe` (`Read` has no write constructor).
- **Validity:** every stored game satisfies `Valid (toGame r)`. This follows from `WF` (every row is `Checked`), which is an invariant by LAPI-06's `Api.wf_invariant`. The `Checked` evidence at each write comes from the domain's `preserves` theorems (LAPI-04). No simulation to a separate store is needed.
- **Unique and fresh ids:** from LeanDB's id law (ids are fresh AUTOINCREMENT values, never reused), stated in `DbState`.
- **Isolation.**
  - `SameView p` is **defined from scoped queries**: the rows of `GameRow` with `visibleTo p`, `p`'s receipts, and the token and player tables (public in the view today).
  - Each endpoint's `Isolated` obligation is discharged with LeanDB's **frame lemma**: a query scoped to `p` answers the same in two states that agree on `p`'s rows.
- **Existence privacy:** corollary, as now.
- **New: restricted logical reads.** Every query a `gamesApi` endpoint issues on behalf of `p` has a predicate that implies `visibleTo p`, or reads a table in `p`'s public view. This is a statement about the `Pred` values in each program, so other players' games are never fetched, not only never answered (DESIGN §6.3). Prove it per endpoint, or by a checker over the program's queries if LeanDB's footprints make that mechanical.

## Acceptance criteria

- `api_reads_safe`, `api_allValid`, `api_uniqueIds`, `api_noninterference` and `api_existence_private` proved about `gamesApi : Api (DbState Games)`, audited, registered in `Evidence.lean`.
- `api_restricted_reads` proved and registered as a new claim.
- Each also stated of the running service through LAPI-06's corollaries.

## Tests

- A regression that fails the isolation proof: an endpoint variant reading `GameRow` unscoped must not satisfy `Isolated`. Pinned with `#guard_msgs`, as LAPI-03's wrapper test does.

## Compatibility

Proof-only.
