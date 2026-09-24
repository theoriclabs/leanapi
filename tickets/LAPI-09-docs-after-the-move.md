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
- **docs/blog/leanapi.md:**
  - "What exactly is proved" now says the theorems hold of the running service, relative to LeanDB executing as its meaning;
  - retry safety is proved on the API itself;
  - the examples use `Read`/`Txn` signatures.
- **CHANGELOG.md** and a release note for the version that ships it.

## Acceptance criteria

- `check_readme.sh` passes (README examples compile against the new API).
- Every theorem name in README, ENDPOINTS, QUERIES and the blog exists and is registered.
- No document mentions `Model.step`, `App/Service.lean` or the app differential test as current.

## Compatibility

Docs only.
