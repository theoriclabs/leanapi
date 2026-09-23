# 0015. Per-caller isolation claim (Q4)

Status: accepted (provisional), M7, 2026-09-23. Refines [0009](0009-q4-isolation-claim.md).

For an exported proved route and a request that authenticates as player `p`,
if two model worlds have the same `SameView p` (sessions, visible games in
order, `p`'s receipts, player ids, and next game id), their complete responses
are equal. Other players' views may differ. This is proved for private-games
by `PrivateGames.Model.step_noninterference_caller`, and from the reusable
`ScopedApp.step_noninterference_caller` by `generic_isolation_caller`.
The notes-with-sharing example also instantiates the reusable theorem.

The stronger `SameViews` theorem assumes **every** player's view matches. It
proves both response equality and preservation of `SameViews` in successor
worlds. That premise does not cover arbitrary changes to a game hidden from
`p` but visible to its participants. Decision 0009's assertion that one
caller's matching view is preserved in successor worlds remains open; the
proved caller-only result is response equality for one request.

The observation is status, all headers and body bytes. The next game id is
part of `SameView p`, so sequential ids remain a known information release.
The claim excludes timing, logs, middleware, account routes, and native/model
refinement, as specified in [EVIDENCE.md](../../EVIDENCE.md).
