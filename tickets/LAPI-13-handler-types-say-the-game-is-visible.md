# LAPI-13: Handler types say the game is visible to the caller: `GameView me`

**Repo:** theoriclabs/leanapi (and a small LeanDB ask) · **Area:** `examples/private-games` (`Api.lean` view types, `DbApi.lean`), `Storage/Schema.lean` lemmas · **Priority:** P1 · **Size:** M
**Depends on:**
- LAPI-12 part 1 (a `PlayerId` that carries its bound, so `pid (pref p) = p` without a hypothesis);
- for the final form, LeanDB reads returning evidence of their filters (below).

**Enables:** the blog's "an endpoint's type is its specification" covers visibility; simpler per-endpoint isolation obligations in LAPI-07.

## Problem

`readGame`'s type says nothing about *whose* game it returns:

```lean
def readGame (me : Auth PlayerId) (id : Path GameId) :
    Read Games (Except GameError (Versioned GameView))
```

A handler that returns any game, for example one read with `Read.get GameRow id` and no `visibleTo` scope, has the same type. It compiles, and it can be mounted and served. Two things stand in the way today, and both are outside the handler:
- **The noninterference theorem.** It covers only the routes listed in `gamesApi`, and it is checked when the proof files are built, not when the server is. `GamesMain` doesn't import them.
- **Code review.**

So "only the two players can see a game" is not visible where the game is returned.

## Proposal

**Index the view by the viewer.**

```lean
/-- A game as `p` may see it: only a game `p` plays in. -/
structure GameView (p : PlayerId) where
  game : Game
  visible : visible p game = true
```

The JSON is unchanged: `ToJson` ignores `p` and the proof. `GamePage p` has `items : List (GameView p)`. The signatures become:

```lean
def readGame (me : Auth PlayerId) (id : Path GameId) :
    Read Games (Except GameError (Versioned (GameView me.val)))
def listGames (me : Auth PlayerId) (q : QueryParams PageReq) : Read Games (GamePage me.val)
def playMove (me : Auth PlayerId) (rev : IfMatchRequired ETagRev) (body : Body MoveBody) (id : Path GameId)
    (key : KeyHeader) : Tx Games GameError (Replayed (Versioned (GameView me.val)))
-- resign, openGame likewise
```

The type now says: whatever this route answers, the game in it is one that `me` plays in. That is checked when the handler is compiled, wherever it is mounted, including a second route such as `/hehe/{id}`.

**Where the evidence comes from:**
- **Reads: from the query.**
  - LeanDB ask: a read returns each row with evidence that it satisfies the query's filters, e.g. `Read.first q : Read s (Option {r // q.Sat r})` (and `all`/`page` likewise), where `q.Sat r` is the conjunction of the `where'` predicates. This is the same shape as the invariant-evidence ask (review M3; LAPI-12 part 2): LeanDB already applies the filter, so it can return the fact.
  - App lemma: `GameRow.visibleTo_sat : (GameRow.visibleTo p).Sat r → visible p (reconstruct r) = true`. It needs `pid (pref p) = p`, which is unconditional after LAPI-12 part 1.
- **Writes: from the domain.**
  - `playMove` and `resign` keep the participants (`decide_participants`), so visibility carries over from the row that was read.
  - `openGame` makes the caller player `x` of the new game (a lemma, `openGame_visible`).
- **Until LeanDB returns evidence:** decide `visible me.val (reconstruct row)` on the returned row, and answer `.hidden` when it is false. This is redundant with the query and cheap. It also turns a disagreement between LeanDB's SQL and its meaning into a 404 instead of a leak. Remove it when the evidence arrives.

**Scope.** The type rules out *returning* another player's game. It doesn't cover:
- what the choice of error reveals (403 against 404);
- what counts or ids reveal.

The noninterference theorem stays the global statement. The type catches the most common mistake locally, and makes each endpoint's isolation obligation smaller.

The in-memory reference API (`PrivateGames.Api`) may keep the unindexed view until LAPI-08 retires it.

## Acceptance criteria

- The five `DbApi` handlers have the signatures above. The blog's `playMove` signature and `readGame` excerpt show `GameView me.val`.
- A `#guard_msgs` test: a handler that reads a game with `Read.get GameRow id` (no scope) and returns it as `Versioned (GameView me.val)` does not compile.
- After the LeanDB evidence lands, `DbApi.lean` has no runtime visibility check.
- The JSON is byte-identical. The differential test and the HTTP tests (both services) pass unchanged.
- `check_blog.sh` passes the same blocks as before.

## Tests

- The `#guard_msgs` test above.
- The existing differential and HTTP tests (same bytes).

## Compatibility

- **No wire change.** Handlers that build a `GameView` must now supply the proof. Inside the example, that is all of them.
