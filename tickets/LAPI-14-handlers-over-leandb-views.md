# LAPI-14: Handlers over LeanDB's row-level views; retire the prototype

**Repo:** theoriclabs/leanapi · **Area:** `LeanApi/Http/DbEndpoint.lean`, `api!`, `examples/*` · **Priority:** P1 · **Size:** L
**Depends on:** LeanDB M16 (`policy%`, read and write views, their laws), LeanDB M15a/M15b. **Enables:** DESIGN §7.5's theorems for every example; LAPI-07 becomes a corollary; LAPI-13 is subsumed.

## Problem

Row-level policies live in a LeanAPI prototype (`examples/policy-view`), and each example built its own write view (`TxAs`, `TxnAs`/`Seen`/`Owns`, `ProjRead`). That works, and the bypasses are compile errors, but:
- **The rule is written twice.** A policy's `rule` and its SQL `scope` are separate definitions, and nothing proves they agree.
- **Isolation is a runtime guarantee.** It is enforced by the types and tested, but not proved about the running service: the laws (restricted reads, frame, write confinement) are DESIGN §7.5 work in LeanDB.
- **The write views diverge.** Three examples, three designs.
- **Unscoped programs aren't flagged.** `api!` accepts an endpoint whose program reads the unscoped schema.

## Proposal

When LeanDB M16 lands:
1. **Handlers over views.** A handler's program is over the actor's view: `(me : Auth P) → … → <LeanDB read or write view for me.val>`. `DbHandler` instances run it with the actor authentication produced; `Auth`'s constructor is private (done), so `me` can't be forged.
2. **Isolation for every route, once.** `Api.noninterference` specialised to views: an API whose authenticated programs are all over views is noninterfering for `SameView p := st₁.restrict p = st₂.restrict p`, with the declared releases, from LeanDB's frame law. There's no per-endpoint obligation for database access.
3. **Coverage.** `api!` over a schema with policies refuses an endpoint whose program is over the unscoped schema, unless it is marked trusted (authentication, sign-up, seeding). The server serves only the API it was given, so the routes reachable over HTTP and the routes covered by the proof are the same set (the `/hehe` gap).
4. **Migrate and retire.**
   - Move private-games, the help desk, billing and scheduling onto LeanDB's `policy%` and views.
   - Delete `examples/policy-view` and the examples' local views.
   - Prove each example's headline isolation claim as a corollary of item 2, and move it from **Planned** to **Proved** in its post.
   - The main post's `api_noninterference` and `api_restricted_reads` (LAPI-07) follow the same way.

## Acceptance criteria

- No example defines its own view type, and `examples/policy-view` is gone.
- Each example's post lists isolation (and write confinement, where relevant) under **Proved**, citing the corollary, and the blog check passes.
- A `#guard_msgs` test: `api!` refuses an unscoped program unless it is marked trusted.
- CI passes, including the axiom audit.

## Compatibility

Breaking for the examples' internals (their views are replaced); no wire change.
