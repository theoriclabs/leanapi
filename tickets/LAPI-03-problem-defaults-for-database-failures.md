# LAPI-03: `ToProblem` defaults for LeanDB's typed failures, safe for isolation

**Repo:** theoriclabs/leanapi · **Area:** `LeanApi/Http/Endpoint.lean` (or a `LeanApi/Db` module) · **Priority:** P1 · **Size:** M
**Depends on:** LeanDB M14 failure types (`InsertError`, `UpdateError`, `SetError`, `AppendError`, `DeleteError`), LAPI-02.

## Problem

LeanDB M14 gives every write its own failure type, derived from the schema (QUERIES.md §3.3). An endpoint can map those failures to its own domain errors with `orAbort`, as the examples do. But many endpoints want to expose them directly (`Txn s (InsertError User) …`), and then each app would write the same `ToProblem` instances with its own status choices.

The payloads are also a trap. The holder of a clashing unique key, the current row after a lost compare-and-swap, and the table that still references a row are exactly what a caller needs. They can also reveal another user's data. An endpoint that answers `409` with `Location: /users/17` has told the caller that user 17 exists and holds that key. That breaks `Api.noninterference` for any view that does not include it.

## Proposal

**Default instances**, with typed statuses and **no payload by default**:

| Failure | Status | Default body |
|---|---|---|
| `InsertError.duplicate ix _` | 409 | detail names the index (`byName`), not the holder |
| `InsertError.missingRef fk` | 422 | `errors: [{loc: "body.<field>", msg: "does not exist"}]` |
| `UpdateError.stale _` | 412 | "changed since" |
| `UpdateError.gone`, `SetError.gone`, `AppendError.gone`, `DeleteError.gone` | 404 | none (same as a missing resource) |
| `UpdateError.duplicate`, `SetError.duplicate` | 409 | as for insert |
| `UpdateError.missingRef`, `SetError.missingRef` | 422 | as for insert |
| `AppendError.notAppend list` | 409 | names the list field |
| `DeleteError.restricted _ _` | 409 | "still referenced", without saying by what |

**Opt-in payloads**, as wrappers whose types show what they reveal:
- `WithHolder (InsertError α)` adds `Location` of the holder (needs `LocationOf α`);
- `WithCurrent (UpdateError α)` adds the current `ETag` and body (needs `ToResponse (Stored α)` and a version);
- `WithReferrers (DeleteError s α)` names the referencing tables and counts.

An endpoint using them states it in its signature, and the isolation obligation (`Isolated`) then requires the payload to be visible to the caller. For example, the holder must be in the caller's view. The proof fails otherwise, which is the point.

## Acceptance criteria

- The default instances exist for all five failure types, with statuses in `ErrorStatus` (typed 4xx).
- The three wrappers exist, with the payload in the response only when the wrapper is used.
- A test endpoint `Txn s (InsertError User) (Created UserView)` answers 409 on a duplicate name, with no `Location` and no user id in the body.
- **Isolation check.** For a test API whose view hides other users, `Api.noninterference` goes through with the defaults. The same proof with `WithHolder` fails at the payload obligation (a `#guard_msgs` test pins the failure).

## Tests

- Each failure constructor answers its status and body (a table-driven HTTP test over a small schema).
- Two worlds differing only in another user's row holding the key give identical 409 bodies under the defaults.

## Compatibility

Additive. Endpoints that map failures with `orAbort` are unaffected.
