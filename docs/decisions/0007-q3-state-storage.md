# 0007. State-based storage with a revision (Q3, first slice)

Status: accepted (provisional), M3, 2026-09-22.

## Decision

- The unit of state is the **game aggregate**: participants, time control,
  move list, resignation and a **revision** `rev`.
- `rev` is part of `Valid`: `rev = moves.length + (1 if resigned)`. Every
  accepted transition bumps it by exactly one (`playMove_rev`), so the
  revision is also a count of transitions. This makes `ETag`/`If-Match`
  meaningful and gives compare-and-swap a key (M4, M5).
- Storage stores the current state (one row plus its move list), not an
  event log. Loading re-validates with `validB`.
- An event log (append-only moves, state as a fold) is a later option. The
  domain already stores moves in order, so the log is the move list: a
  future mapping could store the log alone and derive the rest.

## Consequences

Cross-aggregate rules (e.g. "a player has at most N open games") are not
modelled in this slice. They would need a transaction over several aggregates
or a separate counter row, which is Q5 territory.
