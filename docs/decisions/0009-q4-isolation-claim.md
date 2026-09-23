# 0009. The isolation claim (Q4)

Status: superseded by [0015](0015-q4-caller-isolation.md), M7,
2026-09-23. Written before the proof; its successor-view clause has not been
established under the one-caller premise.

## Candidates (DESIGN §6.3)

| Property | Holds here? |
|---|---|
| Authorized output: every returned game is visible to the caller | Implied by the claim below |
| Response noninterference: changes to hidden data do not change the caller's response | **Claimed** (single request) |
| Restricted logical reads: execution reads only visible rows | Claimed for the model (`load` reads only `visibleGames`, own receipts, player ids). Natively: the SQL predicate. **Assumed** for SQLite's physical execution |
| Trace noninterference across request sequences | Not claimed. Later work |

## The claim

For the exported proved routes (`POST /games`, `GET /games`,
`GET /games/{id}`, `POST /games/{id}/moves`,
`POST /games/{id}/resignation`) and any request `r`:

> If two worlds `w₁`, `w₂` agree on the caller's **view** (the same
> sessions, the same games visible to the caller in the same order, the
> caller's own receipts, the same set of player ids, and the same next game
> id), then `step r w₁` and `step r w₂` produce **the same response** (status,
> headers and body), and the resulting worlds again agree on the view.

`view` is defined by `sameView` in `PrivateGames/Model/Isolation.lean`.
"Hidden data" means every game the caller does not participate in, plus other
actors' receipts. Changing, adding or deleting them cannot change any
response the caller sees.

**Observation:** the full `Res`: status, every header (including `ETag`,
`Location`, `Allow`, `WWW-Authenticate`) and the body bytes (including counts
and the `total` in listings).

**Existence privacy (part of Q4):** a game that exists but is not visible
yields the same response as a game that does not exist. This is an instance
of the theorem (a world without the game has the same view) and also a
separate lemma: every refusal about a hidden game is the fixed `hidden` 404.

## Explicitly outside the claim

- The next game id is part of the view. A new game's id reveals how many games
  exist in total, so ids are a known information release (as with any
  autoincrement key). Fixing it means random ids, a later change.
- Timing, logs, and middleware (decision 0001).
- The unproved account routes (`POST /players`, `POST /sessions`). They reveal
  whether a name is taken, by design.
- Native execution: the claim is about the model. The native service runs the
  same `decode`/`core`; the shell and LeanDB are assumed to refine the model,
  and differential tests are the evidence.
