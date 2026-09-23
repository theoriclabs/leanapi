# 0011. What qualifies as evidence (Q11)

Status: accepted (provisional), M6, 2026-09-22.

## Decision

- Every guarantee is listed in [EVIDENCE.md](../../EVIDENCE.md) with one
  status: **proved**, **checked**, **assumed** or **open** (DESIGN §8.4).
- **Proved** requires a theorem listed in `scripts/audited_theorems.txt`.
  CI runs `scripts/axiom_audit.sh`, which fails on `sorryAx`,
  `Lean.ofReduceBool` / `ofReduceNat` (`native_decide`), and any axiom beyond
  `propext`, `Classical.choice`, `Quot.sound`.
- **Checked** requires a test in `leanapi_tests`, run in CI. The native ≡
  model relationship is evidenced by a differential test. The test is itself
  mutation-checked once, by hand, when it is written: breaking the model must
  make it fail.
- **Specifications live apart from proofs** (`Domain/Game.lean`,
  `Model/Step.lean`, and the `SameView` definition), so weakening a policy is
  its own reviewable diff.
- **Invalidation:** a claim is about the exported proved route table
  (`App.routeTable`) and the middleware stack named in EVIDENCE.md. Adding a
  route to the table puts it under the theorems automatically, because they
  quantify over every request. Adding a plain `IO` route outside the table
  makes it unproved; EVIDENCE.md must list it. M7 turns this list into a
  build-time report.
