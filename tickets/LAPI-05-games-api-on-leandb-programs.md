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
