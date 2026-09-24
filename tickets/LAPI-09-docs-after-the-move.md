# LAPI-09: README, design docs, evidence and the blog post after the move

**Repo:** theoriclabs/leanapi · **Area:** docs · **Priority:** P2 · **Size:** S
**Depends on:** LAPI-08.

## Problem

After LAPI-01…08, several documents describe an architecture that no longer exists:
- a reference model separate from the running service;
- a native service checked by a differential test;
- `Reads`/`Writes` over an in-memory state as the only effects.

## Proposal

Update, each against what the code then says:
- **README.md:** the private-games section (the theorems hold of the running service, relative to LeanDB's trusted step); a `Read`/`Txn` example in "From a domain rule to a proof"; features table; "Limits worth knowing".
- **docs/ENDPOINTS.md:** principle 4 (state backends: `Store` and LeanDB programs), principle 7 (the carry-over theorem).
- **DESIGN.md §7.4** and **docs/QUERIES.md §7:** from vision to status; what shipped, what remains.
- **EVIDENCE.md prose:** the trusted base (generated tables are handled by LAPI-08).
- **docs/blog/leanapi.md** is already written for the finished system (2026-09-23). Its examples are the specification the implementation must meet: `scripts/check_blog.sh` checks every `lean` block against the code (verbatim excerpts, exact theorem statements, compiling examples). On 2026-09-23, 3 of 12 blocks passed. After LAPI-02…05 the code blocks follow `DbApi.lean` (`Tx`, `DbApi`/`dbapi!`, receipts looked up, not claimed first), and 9 of 13 pass. The four theorem statements wait on LAPI-06, 07 and 08. At LAPI-08, point the `DbApi.lean` excerpts at `Api.lean`. If the implementation settles on different names or shapes, update the post and keep the check passing, rather than weakening the check.
- **CHANGELOG.md** and a release note for the version that ships it.

## Acceptance criteria

- `check_readme.sh` passes (README examples compile against the new API).
- `check_blog.sh` passes, and is added to CI next to `check_readme.sh`.
- Every theorem name in README, ENDPOINTS, QUERIES and the blog exists and is registered.
- No document mentions `Model.step`, `App/Service.lean` or the app differential test as current.

## Compatibility

Docs only.
