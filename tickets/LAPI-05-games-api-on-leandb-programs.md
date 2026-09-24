# LAPI-05: `gamesApi` over LeanDB programs, answering byte for byte as today

**Repo:** theoriclabs/leanapi · **Area:** `examples/private-games/PrivateGames/Api.lean` · **Priority:** P0 · **Size:** L
**Depends on:** LAPI-02, LAPI-04. **Enables:** LAPI-07, LAPI-08.

## Problem

`gamesApi` (`Api.lean`) is written over the in-memory `Model.World`, and the production service is a separate implementation (`App/Service.lean`, `Storage/Repo.lean`). The goal is one definition: `gamesApi` over the LeanDB schema, served from SQLite by `Api.serveDb`, with its pure meaning over `DbState Games`.

## Proposal

Rewrite the five endpoints as LeanDB programs (QUERIES.md §3.6):

| Endpoint | Effect | Program |
|---|---|---|
| `readGame` | `Read Games (Except GameError (Versioned GameView))` | `first` over `GameRow`, scoped by `visibleTo me` and the id |
| `listGames` | `Read Games GamePage` | `page` over the same scoped query, ordered by id; total and page from one snapshot |
| `openGame` | `Txn Games GameError (Replayed (Created (Versioned GameView)))` | `exists` on the opponent, `insert` of a `Checked GameRow` (from `Valid.preserved_openGame`), receipt |
| `playMove` | `Txn Games GameError (Replayed (Versioned GameView))` | scoped `first`, domain `playMove` (revision checked there), `patch` of `moves` and `rev` on the `Current` row, receipt |
| `resign` | `Txn Games GameError (Replayed (Versioned GameView))` | as `playMove`, patching `resigned` and `rev`; a second resignation answers without writing |

**Authentication:** `Authenticates Games PlayerId` looks the token digest up with `lookup TokenRow.byDigest`, a read program, in the request's transaction.

**Idempotency receipts are a typed insert** into `ReceiptRow` (unique `byKey`), made **before** deciding. The code is fixed by the blog post's `keyed` example.
- **Claim:** insert a pending receipt (`ReceiptRow.claim`, status 0).
- **Clash:** `duplicate .byKey held` is the replay. Replay `held`'s recorded answer, or refuse with `keyReused` (422) if the fingerprint differs.
- **Decide and record:** on a successful claim, decide, then `patch` the claim with the answer (`status`, `body`). The `patch` writes no unique or reference field, so only `.gone` needs handling.
- **Failures:** `missingRef .actor` becomes `hidden`. A refused request aborts the transaction, claim included.

This replaces `keyed`'s hand-written receipt lookup, and keeps the receipt in the same transaction as the change, as the native service does today (`Repo.lean:124-163`). The table's columns are unchanged.

**Failure mapping is exhaustive** by `orAbort`, over the types LAPI-04 generates. For example, `playMove`'s `patch` writes no unique or reference field, so only `.gone` needs handling.

## Acceptance criteria

- `gamesApi` has type `Api (DbState Games)` and is served by `Api.serveDb` in `GamesMain` instead of `App/Service.lean`.
- **Byte for byte.** The differential test compares three systems on the same random probes (with faults):
  - the new `gamesApi` served from SQLite;
  - the current in-memory `gamesApi` (kept as the reference until LAPI-08);
  - the current native service.

  It requires 0 mismatches on status, `ETag`, `Location`, `Idempotent-Replayed`, `Allow`, `WWW-Authenticate` and body, over at least 400 probes exercising every status.
- All existing private-games HTTP tests pass against the new service (`tests/Tests/Games.lean`): concurrency, restart-after-commit replay, revocation, stored-invalid-row handling.
- `Api.describe` shows the `Read`/`Txn` signatures.
- The blog post's excerpts of `Api.lean` (`GameRow.visibleTo`, `readGame`, `gamesApi`, `keyed`) and `playMove`'s signature pass `scripts/check_blog.sh`.

## Tests

- **Simultaneous moves on one revision.** Exactly one commits and the rest answer 412, now through LeanDB's `BEGIN IMMEDIATE` plus the domain's revision check.
- **Concurrent requests with one key** produce one transition and one receipt; the others replay.
- **Restart after commit.** A retry after a restart replays the receipt.

## Compatibility

HTTP behaviour identical, checked by the differential test. The database schema is unchanged apart from LAPI-04's declarations. Existing databases keep working.

## Status (2026-09-23): done on LeanDB M14b (`d33d067`), with two recorded deviations

Branch `lapi-02-read-effects` (stacked). `examples/private-games/PrivateGames/DbApi.lean`:
- The five routes as LeanDB programs over `DbState Games`. `listGames` and `readGame` are `Read`s, scoped by `GameRow.visibleTo`. `openGame`, `playMove` and `resign` are `Tx`s.
- `Checked GameRow` comes from `GameRow.checkedOpen`/`checkedStep` (the domain proofs), with no runtime check. The `duplicate` arms are `nomatch` (`Unique GameRow` is empty).
- Authentication is `lookup TokenRow.byDigest`, a read program, inside the request's snapshot or transaction.
- `GamesMain` serves the game routes from `gamesApi` over `DbConns`. The unproved account routes stay on the repository. `describe` prints the `Read`/`Tx` signatures, and I checked it by running the binary and exercising open, replay and move over curl.

Acceptance:
- **Byte for byte:** the differential test now compares four systems (model, in-memory `gamesApi`, native service, LeanDB-program `gamesApi`) on the same 400 random probes with faults. It found 0 mismatches on status, the compared headers and body, in 6 consecutive runs, and statuses 200/201/401/404/405/409/412/415/422/428 were all exercised.
- **All private-games HTTP tests** run against both services (`Tests.Games.runWith .native` / `.dbapi`): simultaneous moves (exactly one wins, 7 × 412), concurrent same key (one transition), restart-after-commit replay, invalid stored row (500 without detail). 407 tests pass.
- Revocation-between-admission-and-commit is a repository-level test and runs for the native service only. For programs, admission and commit are one transaction.

**Deviation 1 (location):** the new API is `PrivateGames.DbApi.gamesApi` (type `DbApi Games`, whose `toApi : Api (DbState Games)`), next to the reference `PrivateGames.Api.gamesApi`, which this ticket keeps until LAPI-08. So the blog's `excerpt examples/private-games/PrivateGames/Api.lean` blocks still fail (`check_blog.sh`: 3/12, unchanged, not in CI). They pass once LAPI-08 moves `DbApi.lean` to `Api.lean`.

**Deviation 2 (receipts):** receipts are looked up by `ReceiptRow.byKey`, then inserted with the change, inside one `BEGIN IMMEDIATE` transaction. They are not claimed first. Claim-first cannot meet the byte-for-byte criterion: it records a receipt for requests that answer *without* writing (a repeated resignation), so a later request with that key and a different body would answer 422 where the reference decides afresh. Under the single writer the two designs are equally race-free. To adopt claim-first, first change the reference and model semantics (record answers for non-writing keyed requests), then this code and the blog's `keyed`.
