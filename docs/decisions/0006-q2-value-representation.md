# 0006. Valid values: proof fields for decidable bounds, smart constructors everywhere (Q2)

Status: accepted (provisional), M3, 2026-09-22.

## Decision

- **Bounded scalars carry proof fields** (`Cell : i < 9`,
  `TimeControl : 1 ≤ minutes ≤ 180`). The bound is decidable, the proof is
  erased at runtime, and domain proofs use it without re-checking.
- **Identities are plain newtypes** (`PlayerId`, `GameId`). A well-formed
  id carries no authority (DESIGN §2.1), so there is nothing to prove about it
  beyond positivity, which `make` checks.
- **Every value has exactly one smart constructor** `make : raw → Except
  String α`. Both boundaries go through it:
  - HTTP: `instance : SmartCtor α raw` gives `FromParam` / `FromBody`
    (M1 extractors), with the error at a field location.
  - LeanDB: `ColCodec.via (·.raw) make` (M4 codecs). A stored value that
    fails `make` is a typed decode error, never a crash.
- **Round-trip laws** `make (raw v) = .ok v` are proved per value type
  (`Cell.make_i`, `TimeControl.make_minutes`, `GameId.make_n`). The codec
  round-trip law in M4 is stated on top of them.
- **Multi-field invariants** (`Valid` for `Game`) are a `Prop` with a
  Boolean check `validB` and `validB_iff`. The check runs on every load and
  before every write; the `Prop` is what theorems use.

## Consequences

Private constructors were not needed: no API constructs a `Cell` without
`make` or a proof. Private constructors do not sandbox Lean code anyway
(DESIGN §4.3).
