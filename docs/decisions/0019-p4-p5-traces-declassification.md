# 0019. Trace properties and time (P4), declassification (P5)

Status: accepted (provisional), M12, 2026-09-23. Settles [PROPERTIES.md](../PROPERTIES.md) P4 and P5 for the first library.

## P4: how much temporal structure

The library encodes traces as **finite request sequences** and nothing
more: `runTrace` over `Sys`, `Keyed.run`, and private-games' `runReqs`.
Every trace property is proved by reducing it to an invariant or a step
property of a derived system (PROPERTIES.md §6.1):

- keyed replay after any interleaving: receipts are stable under every
  step (`keyed_stable`), a step property, then induction over the trace;
- trace noninterference: single-step NI plus the unwinding condition
  (`Observation.trace_ni`), then induction.

Time stays in `Env`. Properties that depend on clocks (expiry, retention
windows) are stated over `Env` explicitly when an app needs them; the
library has no temporal logic, no fairness and no liveness. That keeps it a
proof library, not a model checker. Receipt expiry remains open in
EVIDENCE.md.

## P5: declassification

Allowed releases are stated **in the view**, not as exceptions to the
property: anything an observer may learn is part of `view`, and NI is
proved over that view. private-games releases the next game id this way
(`nextGame` is in every player's view, decision 0009), and whether a
player exists (`players`).

Two guards keep this from becoming vacuous:

- the hiddenness witness (`Observation.Hidden`, `gamesObs_hidden`) must
  still hold after the release is added: something must remain hidden;
- `NIPackage` needs an `Enabled` companion with a satisfiable
  precondition.

The coalition trace theorem (`trace_noninterference`) excludes requests by
players outside the coalition. An outsider's write can legitimately change
what the coalition sees (opening a game with a member), which is an
intended release on writes, not only on views. Stating that release
(for example "an outsider may add a game in which a member participates")
is the remaining open part of P5 and is listed in EVIDENCE.md.
