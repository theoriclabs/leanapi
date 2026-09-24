# LAPI-10: Retry fingerprints computed by the framework, not written by hand

**Repo:** theoriclabs/leanapi · **Area:** `LeanApi/Http` (inputs), `examples/private-games` · **Priority:** P1 · **Size:** M
**Depends on:** none (simpler after LAPI-08, when one implementation is left). **Enables:** LAPI-08's `api_keyed_replay_after` rests on a fingerprint that can't miss an input.

## Problem

Whether a retry replays or is refused (`keyReused`, 422) depends on a fingerprint of the request, stored with every receipt. Each endpoint writes its fingerprint by hand, as a string:

```lean
s!"openGame|{body.val.opponent.n}|{body.val.tc.minutes}"      -- DbApi.lean:83
s!"playMove|{id.val.n}|{rev.val.rev}|{body.val.cell.i}"      -- DbApi.lean:126
s!"resign|{id.val.n}"                                        -- DbApi.lean:138
```

The same strings are written three times: `DbApi.lean`, `Api.lean:172/198/211` and `App/Core.lean:181-183`. Only the differential test keeps them equal. Nothing ties a fingerprint to its endpoint's inputs:
- **An input missing from the string** makes two different requests with the same key look identical: the second replays the first's answer. Nothing fails when an endpoint gains an input and its fingerprint doesn't.
- **A change of format** (order, separator, how a field renders) makes every stored receipt stop matching its retries. They then answer 422 instead of replaying (docs/BOUNDARIES.md, D10).
- The operation is also a string (`op.name`) in the receipt row.

## Proposal

**The framework computes the fingerprint; handlers never write one.**
- A framework input, `Idempotency` (replacing the app's `KeyHeader := Header "idempotency-key" (Option IdemKey)`), reads the `Idempotency-Key` header. It gives the key together with the request's fingerprint and the endpoint's identity (method and route template).
- The fingerprint is a hash (SHA-256) of the request **as the endpoint reads it**:
  - method and route template;
  - the path parameters;
  - the query parameters, sorted;
  - the body: JSON re-serialized canonically (sorted keys, no insignificant whitespace), other media types as raw bytes;
  - `If-Match`, and every header the endpoint's signature declares (`Header n α`), except the key itself.
- **It is complete by construction.** A handler sees nothing of the request that the fingerprint leaves out. `Auth` is the receipt's actor, already part of its key. `Now` and `FreshToken` come from the environment, not the request.
- **It is versioned.** The stored value is `v1:<hex>`. A receipt with another version is compared using that version's function. An app that has receipts from before this change registers its old function as `v0` for as long as it needs to.
- **The receipt's operation** is the endpoint's identity from the framework, not a string the app picks.

private-games:
- `keyed` takes the `Idempotency` value, and `keyedFor` no longer takes a canonical string.
- The three hand-written fingerprints are deleted.
- The model and the reference (until LAPI-08 retires them) take the fingerprint from the same framework function applied to the probe's request, so the differential test still compares like with like.

## Acceptance criteria

- No application code builds a fingerprint or an operation name. `grep 'fingerprint' examples/` finds only the receipt row's field.
- For each private-games keyed endpoint, requests that differ in any single input (path parameter, query parameter, body field, `If-Match`, declared header) have different fingerprints.
- Adding a `Header` input to an endpoint changes its fingerprint without any change to the endpoint's code (a test endpoint).
- JSON bodies that differ only in key order or whitespace have equal fingerprints.
- The existing replay and refusal tests pass unchanged. That includes concurrent same-key requests and replay after restart.
- A receipt stored with a `v0` fingerprint is still replayed when `v0` is registered (a test opens a database written before the change).

## Tests

- A unit test of the canonical form (JSON key order, whitespace, sorted query parameters).
- The per-input test above, generated from each endpoint's declared inputs.
- `tests/Tests/Games.lean`: the keyed tests, run against both services.
- The differential test, with the model and reference using the framework fingerprint.

## Compatibility

- **Receipts written before the change** match only if the app registers its old fingerprint as `v0`. Otherwise a retry of a request made before the upgrade answers 422 instead of replaying. private-games registers `v0` (its current strings) until receipts from before the change no longer matter.
- **Stricter than today, by design:** two requests whose bodies differ in a field the decoder ignores now have different fingerprints, so the second answers 422.
