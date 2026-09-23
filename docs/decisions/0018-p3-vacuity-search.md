# 0018. Vacuity checks as proofs or as tests (P3)

Status: accepted (provisional), M10, 2026-09-23. Settles [PROPERTIES.md](../PROPERTIES.md) P3.

**Spike.** Plausible (`leanprover-community/plausible`, tag `v4.33.0`)
builds on toolchain 4.33. Its `deriving Arbitrary` fails on structures with
proof fields (`Cell` with `isLt : i < 9`, `TimeControl` with its bounds),
which are exactly the domain values that matter (decision 0006).

**Decision.** Keep our own small exhaustive generator, `LeanApi.Props.Enumerate`,
with a deriving handler that supports proof fields whose statement is
decidable (a candidate is kept only when the statement holds). Exhaustive
search over a small bound also gives a definite report ("searched 15 worlds
× 1 environment × 1 request") rather than a sample. Plausible is not a
dependency.

**Both, for different jobs.**

- Search is a **test**. `#check_invariant` and `checkHidden` find vacuity,
  counterexamples to induction and missing hiddenness witnesses before a
  proof is attempted. They report what they searched. Proofs never depend
  on them, and search results are listed as Checked, never Proved.
- A witness that matters for a claim is then **proved** as a plain `example`
  or theorem (for example `existence_private` rests on `withHidden_view`,
  which exhibits two different worlds with the same view).

**Regression targets** (tests in `tests/Tests/Props.lean` and
`tests/Tests/PropsCommands.lean`):

- unique ids without `Fresh`: a CTI whose world has `next` equal to an
  existing id, reported as unreachable (strengthen, not false);
  `Fresh ∧ UniqueIds` has none;
- review C1: the all-players view has no hiddenness witness, while the
  caller view has one for every observer.
