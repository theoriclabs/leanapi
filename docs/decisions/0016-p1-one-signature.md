# 0016. One signature or several (P1)

Status: accepted (provisional), M8, 2026-09-23. Settles [PROPERTIES.md](../PROPERTIES.md) P1.

**Decision.** Keep both signatures, with a one-way lifting.

- `LeanApi.Props.Sys` (world, request, response, environment, `step`, `init`)
  is where every generic property and the invariant theory live:
  `Reachable`, `Invariant`, `Inductive`, the operator algebra, `pre`,
  `WeakestInductive`, `CTI`.
- `LeanApi.Proofs.ScopedApp` stays the pipeline-specific signature
  (route → authenticate → decode → load → core → run). Its isolation
  theorems are cheap because the pipeline is fixed.
- `ScopedApp.toSys A init` makes every scoped app a `Sys` with `Env := Unit`.
  An app picks its initial worlds.

**Where canonical statements live.** A property whose proof uses the
pipeline (isolation, keyed replay per route) is stated on `ScopedApp`. A
property about reachable worlds, runs or steps (invariants, monotonicity,
generic keyed idempotence) is stated on `Sys`, and apps reach it through
`toSys`. Store-level facts (entity invariants, unique ids) are stated on
the generic `ListStore` and pulled back to an app along a `Simulation`.

**Evidence that `Sys` fits a real app** (the M8 risk). private-games is
instantiated as `gamesSys := gamesApp.toSys gamesInit`, and two invariants
that were only checked at runtime are now proved about every reachable
model world: `allValid` and `uniqueIds`. The only app-specific proof is
`core_writeOk` (inserts are valid, updates keep ids). The rest is the
library: `ListStore.allOf_invariant`, `ListStore.ids_invariant` (with the
`Fresh` strengthening) and `Invariant.pullback`.

**Revisit when** an app needs a non-`Unit` environment (clocks, expiry): the
`toSys` lifting would then take the environment from the request context.
