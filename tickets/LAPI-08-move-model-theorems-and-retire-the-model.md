# LAPI-08: Move the remaining model theorems; retire `Model/`, the native service and the app differential test

**Repo:** theoriclabs/leanapi · **Area:** `examples/private-games`, `LeanApi/Proofs`, `tests` · **Priority:** P1 · **Size:** L
**Depends on:** LAPI-07. **Enables:** LAPI-09.

## Problem

Three theorems are still proved only on the reference model (`PrivateGames/Model/`):
- **keyed replay**, immediately and after any interleaving: `keyed_replay`, `keyed_replay_after`;
- **move logs only grow:** `movesGrow`;
- **coalition trace isolation:** `trace_noninterference`, `step_view_caller`.

While they remain there, so does everything they need:
- `Model/` (about 1,500 lines of model and proofs);
- the `ScopedApp` instance `gamesApp` (`Model/Generic.lean`);
- the native service (`App/Service.lean`, `Storage/Repo.lean`);
- the app-level differential test (`tests/Tests/Differential.lean`).

## Proposal

**Move the theorems** onto `gamesApi : Api (DbState Games)`:
- **Keyed replay.** With receipts as a typed insert (LAPI-05), replay after any interleaving follows from receipts only growing, which is a frame lemma: no endpoint writes `ReceiptRow` except by insert, and none deletes. The generic `Keyed` transformer (`LeanApi/Props/Keyed.lean`) is not needed for private-games; keep it only if another example uses it.
- **`movesGrow`.** Every write to `GameRow` is a `patch` whose `moves` value extends the stored one (the domain's `playMove_extends`/`resign_extends`), or an insert.
- **Trace isolation** by unwinding over `Api.toSys` (`Observation.trace_ni`), with `step_view_caller` restated on `DbState`.

**Retire:**
- `Model/` (all of it), `App/Service.lean`, `Storage/Repo.lean`, and `App/Core.lean`'s `decode`/`core` if nothing else uses them;
- the `gamesApp` `ScopedApp` instance;
- `LeanApi/Proofs/Scoped.lean`, if `Notes/Shared.lean` is the only other user and moves to typed endpoints (otherwise keep it as the pipeline-specific signature, with decision 0016 updated);
- `tests/Tests/Differential.lean`. **Keep one end-to-end HTTP test** that drives the served API through every status. LeanDB's harness owns "execution equals meaning".

**Evidence.** Regenerate EVIDENCE.md from the registry. Every private-games claim is now about `gamesApi` and, by LAPI-06, about the running service. Update the audit list to remove retired theorems and add the moved ones.

## Acceptance criteria

- `api_keyed_replay`, `api_keyed_replay_after`, `api_movesGrow` and `api_trace_noninterference` proved about `gamesApi` over `DbState`, audited and registered. `api_keyed_replay_after`'s statement is the blog post's (checked by `scripts/check_blog.sh`).
- The retired files are deleted, and nothing references them.
- CI passes; the axiom audit covers every registered theorem; `gen_evidence.sh --check` passes.
- EVIDENCE.md no longer lists "native ≡ model" as an assumption, only LeanDB's trusted step (LAPI-06).

## Tests

- The end-to-end HTTP test exercises each status (200, 201, 401, 404, 405, 409, 412, 415, 422, 428) against the served API, with the typed probes from today's differential test.

## Compatibility

HTTP behaviour identical: checked by the differential test until it is retired, then by the end-to-end test. Removes public Lean modules (`PrivateGames.Model.*`); nothing outside the example depends on them.
