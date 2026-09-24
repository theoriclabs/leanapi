# LAPI-06: The carry-over theorem: the running service is `Api.step`

**Repo:** theoriclabs/leanapi · **Area:** `LeanApi/Http/Endpoint.lean`, `LeanApi/Props` · **Priority:** P0 · **Size:** M
**Depends on:** LeanDB M15 (`run = denote` for `Read`/`Txn`, well-formedness preserved by every write), LAPI-02. **Enables:** LAPI-07.

## Problem

Every API theorem is about `Api.step`, the pure meaning. For those theorems to be about the running service, one statement must connect the two, and it must say exactly what it assumes. Today that link is "native ≡ model, checked by a differential test" (EVIDENCE.md, trusted base item 1), made separately for each app.

## Proposal

**The framework theorem**, for any `api : DbApi s` (a plain `Api (DbState s)` has no programs to run, only their meaning):

```lean
theorem DbApi.serve_eq_step (api : DbApi s) (hexec : ExecutesAsMeaning s)   -- LeanDB's trusted step, as a named hypothesis
    (hwf : st.WF) (hdone : Completes api env r st) :
    api.served env r st = api.step env r st
```

`DbApi.step` is `api.toApi.step`, so `gamesApi.step` reads as in the blog. `DbApi.served` runs each endpoint's `prog` (`DbProg.exec`) and `Completes` says it met no `DbFault`.

In words: on a well-formed database, when a request completes (no `DbFault`), the running service answers and leaves the database exactly as `Api.step` says.

- `ExecutesAsMeaning` is **LeanDB's single trusted step**, stated per operation: executing an operation on a well-formed state, when it completes, equals its meaning. It is a named `Prop` hypothesis, never an `axiom` (EVIDENCE.md rule).
- **Well-formedness is an invariant of every typed API over LeanDB:** `Api.inductive_of` plus LeanDB's law that every write preserves `WF`. So `hwf` holds of every reachable database.
- **Middleware stays outside,** as today (trusted, EVIDENCE.md item 5). The theorem is about the routed API.

**Evidence.** EVIDENCE.md's trusted base changes:
- item 1 ("native ≡ model, checked") is **replaced** by "LeanDB executes as its meaning (checked once in LeanDB, by its differential harness)";
- private-games no longer carries its own native-vs-model assumption.

## Acceptance criteria

- `DbApi.serve_eq_step` proved with no `sorry`, audited, with `ExecutesAsMeaning` as a hypothesis. Its statement is the blog post's (checked by `scripts/check_blog.sh`).
- `Api.wf_invariant`: `WF` holds in every reachable state of any LeanDB-backed typed API.
- **Corollaries** stated for production, each from the corresponding `Api` theorem and `serve_eq_step`: GET never changes the database; invariants hold of the running database; `noninterference` holds of running responses.
- EVIDENCE.md's trusted base updated as above; `gen_evidence.sh --check` passes.

## Tests

- None beyond the proofs. LeanDB's differential harness is the evidence for `ExecutesAsMeaning`. LeanAPI's own differential test is retired in LAPI-08.

## Compatibility

Proof-only; no runtime change.
