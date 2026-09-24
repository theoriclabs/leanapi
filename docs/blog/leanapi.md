<!--
blog-check prelude
import LeanApi
import PrivateGames.Api
import PrivateGames.ApiProofs
import PrivateGames.ApiIsolation
import PrivateGames.Storage.Schema
import PrivateGames.DbApi
open LeanDb LeanApi LeanApi.Props PrivateGames PrivateGames.Api PrivateGames.Storage
-->
<!--
Every `lean` block below is checked by `scripts/check_blog.sh`, as marked just
above it:
- `excerpt <file>`: the block appears verbatim in that file of the repository;
- `signature <name>`: the block is the exact statement of that declaration;
- `compile`: the block builds on its own.
The code blocks match the LeanDB-backed API (`PrivateGames/DbApi.lean`, which
LAPI-08 moves to `Api.lean`). Four theorem statements describe proofs that do
not exist yet: `api_noninterference` and `api_restricted_reads` (LAPI-07),
`api_keyed_replay_after` (LAPI-08) and `DbApi.serve_eq_step` (LAPI-06). They
wait on LeanDB M15, which gives `DbState` real content in proofs. The check
fails until then. It must pass before this is published.
-->

# LeanAPI

*A FastAPI / Express alternative for Lean 4, with theorems about your whole backend, database included.*

Over the past few days I released a handful of tools for the Lean ecosystem:

- **LeanReact**, for UIs;
- **LeanDB**, a typed database;
- **LeanHttp**, an HTTP client.

This is the next one: **LeanAPI**, a backend framework in the spirit of FastAPI and Express.

Several people have asked what the point is of rewriting all of this in Lean. The short answer: **you can prove properties of a program across system boundaries.**

A backend sits between two systems: the API that clients call, and the database behind it. Most bugs that hurt are in the gaps between them. A check done in one place is forgotten in another, a query returns a row it shouldn't, or a retry writes twice. When the API, the domain logic and the database queries are all Lean, you can state properties about the *whole* system, prove them, and have the proofs hold of the service that is actually running.

I'll show two such properties with a small example, and then how the proofs reach the running service.

## An endpoint's type is its specification

An endpoint is a plain function. Its type tells you what the request does:

<!-- check: signature PrivateGames.DbApi.playMove -->
```lean
def playMove (me : Auth PlayerId) (rev : IfMatchRequired ETagRev) (body : Body MoveBody) (id : Path GameId)
    (key : KeyHeader) : Tx Games GameError (Replayed (Versioned GameView))
```

Read the signature:
- the caller is an authenticated player;
- they must send the revision of the game they saw (`If-Match`);
- the body is decoded and validated as a move;
- the game id comes from the path, and a retry key from a header;
- it is a database transaction (`Tx`) over the `Games` schema: it commits or rolls back as a whole;
- it answers the updated game with its `ETag`, possibly replayed from an earlier identical request, or fails with one of the cases of `GameError`.

There is no request object, response object or SQL in the body. A `GET` endpoint whose handler can write doesn't compile.

## The example: private games

A table of games. Each game has two players, and the rule is simple: **only those two players can see a game.**

The rule, as it appears in the code:

<!-- check: excerpt examples/private-games/PrivateGames/Domain/Game.lean -->
```lean
def visible (p : PlayerId) (g : Game) : Bool := g.isParticipant p
```

The same rule, as a database query, and the one game a player may read:

<!-- check: excerpt examples/private-games/PrivateGames/DbApi.lean -->
```lean
/-- The games `p` plays in. -/
def GameRow.visibleTo (p : PlayerId) : LeanDb.Query Games [GameRow] (Stored GameRow) :=
  (LeanDb.Query.from GameRow).where' fun g => g.val.x == pref p || g.val.o == pref p

/-- The game with id `gid`, if `p` plays in it. -/
def visibleGame (p : PlayerId) (gid : GameId) : Read Games (Option (Stored GameRow)) :=
  Read.first ((GameRow.visibleTo p).where' fun g => g.id == gidRef gid)
```

One endpoint, and the table of all five:

<!-- check: excerpt examples/private-games/PrivateGames/DbApi.lean -->
```lean
/-- One of my games. Someone else's game is indistinguishable from a missing one. -/
def readGame (me : Auth PlayerId) (id : Path GameId) :
    Read Games (Except GameError (Versioned GameView)) := do
  match ← visibleGame me.val id.val with
  | some g => return .ok (versioned g)
  | none => return .error .hidden
```

<!-- check: excerpt examples/private-games/PrivateGames/DbApi.lean -->
```lean
def gamesApi : DbApi Games := dbapi! [
  .post "/games"                       openGame,
  .get  "/games"                       listGames,
  .get  "/games/{id:nat}"              readGame,
  .post "/games/{id:nat}/moves"        playMove,
  .post "/games/{id:nat}/resignation"  resign
]
```

Reading `readGame`:
- `me` is the authenticated player. Without valid credentials the request never reaches the function (401).
- `id` is the `{id}` segment of the path, already decoded and validated.
- `Read Games` means it reads the database and cannot change it.
- It asks for the first game that `me` plays in with that id. The answer is the game or `none`: a game that doesn't exist and a game that isn't theirs are both `none`, a 404.

There are many ways to get this wrong in a normal backend:

- Forget the auth check on one route.
- Check that the user is logged in, but not that the game is *theirs*. Someone who guesses a game id can then watch another person's game.
- Answer **403** for someone else's game but **404** for a missing one. That tells an attacker which ids exist.
- Load every game and filter in code, so one missed filter leaks everything.

Tests catch the cases you thought of. Here we prove that **no code path** reachable through the API does any of this.

### Property 1: you only ever see your own games

<!-- check: signature PrivateGames.Api.api_noninterference -->
```lean
theorem api_noninterference (p : PlayerId) (env : Env) (r : Req) {s₁ s₂ : DbState Games}
    (hv : SameView p s₁ s₂) (ha : AuthenticatesAs p env r s₁) :
    (gamesApi.step env r s₁).1 = (gamesApi.step env r s₂).1
```

In words:
1. Take any request `r` that authenticates as player `p`.
2. Take any two database states `s₁` and `s₂` that look the same to `p`: the same games `p` plays in, and the same session and player tables.
3. They may differ in anything else. Other people's games can be completely different.
4. Then the **entire HTTP response is identical**: status code, every header, every byte of the body.

So nothing `p` receives can depend on data `p` isn't allowed to see. `gamesApi.step` is the whole API: routing, authentication, decoding, the queries and the writes. So this covers every route and every branch, including 401, 404, 405, 409 and 412, not just the happy path.

And a stronger one: the other players' games are never even *fetched*. Every query a request makes on behalf of `p` is restricted to the games `p` plays in:

<!-- check: signature PrivateGames.Api.api_restricted_reads -->
```lean
theorem api_restricted_reads (p : PlayerId) (env : Env) (r : Req) (s : DbState Games)
    (ha : AuthenticatesAs p env r s) :
    ∀ q ∈ gamesApi.queriesOf env r s, q.ScopedTo (GameRow.visibleTo p)
```

Most of the work is the framework's. LeanAPI proves once, for every API written this way, that the response depends only on the caller's view, provided each endpoint meets an obligation computed from its *signature*:
- inputs that don't touch the database are handled automatically;
- `Auth` switches the obligation to "what this player can see";
- what is left for the app is to show that each query is scoped to the player, and LeanDB's laws do the rest.

Three things follow:
- **A guessed game id is indistinguishable from a missing one** (`api_existence_private`).
- **"Deny everyone" isn't a loophole.** A player can always read their own games (`api_read_available`).
- **GET never changes anything**, and this one is free: every API written this way gets it.

<!-- check: signature LeanApi.Api.step_safe -->
```lean
theorem step_safe (api : Api σ) (env : Env) (r : Req) (s : σ) (hm : r.method.Safe) :
    (api.step env r s).2 = s
```

### Property 2: retrying a request is safe

A player makes a move and the network drops the response, so the client retries with the same `Idempotency-Key`. If the server applied the move twice, the game would be corrupted.

The receipt is looked up by its key in the same transaction as the move:

<!-- check: excerpt examples/private-games/PrivateGames/DbApi.lean -->
```lean
def keyed [ToResponse α] (me : PlayerId) (k? : Option Keyed)
    (decide : Txn σ Games GameError (Bool × α)) : Txn σ Games GameError (Replayed α) :=
  match k? with
  | none => do let (_, a) ← decide; pure (.fresh a)
  | some k => do
    match ← Txn.liftRead (Read.lookup ReceiptRow ReceiptRow.Unique.byKey (pref me, k.op, k.key)) with
    | some rc =>
      if rc.val.fingerprint == k.fingerprint then pure (.replay (receiptOfRow rc.val))
      else Txn.throw .keyReused
    | none =>
      let (wrote, a) ← decide
      if wrote then
        let res := ToResponse.toRes a
        let _ ← Txn.orAbort (Txn.insert ReceiptRow (Checked.of
            { actor := pref me, op := k.op, key := k.key, fingerprint := k.fingerprint,
              status := res.status, body := rowBody res } trivial)) fun
          | .duplicate .. => GameError.keyReused
          | .missingRef _ => GameError.hidden
      pure (.fresh a)
```

The receipts table has a unique index on (player, operation, key), so looking a receipt up by it gives one receipt or none. So:
- the first request finds none and decides. `decide` also says whether it wrote; if it did, its answer is recorded together with the change (a request that changes nothing, such as resigning twice, records nothing);
- a retry finds the receipt and replays its answer, or is refused if its body differs (`keyReused`);
- if the move is refused, the transaction rolls back and nothing is recorded, so a corrected retry can go through.

The lookup and the insert are one transaction, and LeanDB runs write transactions one at a time (`BEGIN IMMEDIATE`). So two copies of the same request can't both find no receipt.

The theorem:

<!-- check: signature PrivateGames.Api.api_keyed_replay_after -->
```lean
theorem api_keyed_replay_after (env env' : Env) (r : Req) (rest : List (Env × Req)) (s : DbState Games)
    (hr : KeyedWriteCommits gamesApi env r s) :
    let (answer, s₁) := gamesApi.step env r s
    let s₂ := gamesApi.runAll rest s₁
    gamesApi.step env' r s₂ = (markReplay answer, s₂)
```

In words: once a keyed request has committed, sending it again, after any other requests from anyone, answers exactly what it answered the first time, marked as a replay, and changes nothing.

### Failures have types too

Writes can fail only in the ways their types list, and those come from the schema. Opening a game inserts a row:

<!-- check: excerpt examples/private-games/PrivateGames/DbApi.lean -->
```lean
        let row ← Txn.orAbort (Txn.insert GameRow (GameRow.checkedOpen h hb.1 hb.2)) fun
          | .missingRef _ => GameError.unknownOpponent
          | .duplicate ix _ => nomatch ix
```

A game refers to its players, so the insert can fail with `missingRef`. Games have no unique index, so `duplicate` would need an index that doesn't exist, and `nomatch ix` says so. Add a unique index to games, and this stops compiling until the clash is handled. `GameRow.checkedOpen h …` is the evidence that the new game is valid, from the domain's proof about opening a game. Without it, `insert` doesn't type-check.

## Writing your own properties

These aren't special cases. Your domain rules are properties too, and LeanAPI makes them cheap to state:

<!-- check: compile -->
```lean
structure Board where
  items : List String

invariant Board.Valid (b : Board) where
  bounded : b.items.length ≤ 100

def Board.add (t : String) (b : Board) : Except String Board :=
  if b.items.length < 100 then .ok { items := b.items ++ [t] }
  else .error "board is full"

preserves Board.Valid by Board.add
```

`invariant` declares the rule. From it you also get a runtime check that names the failing field, and a proof that the check and the rule agree. `preserves` proves that every successful `add` keeps the board valid.

Now introduce an off-by-one: change `<` to `≤`. The **build fails**, and Lean shows exactly what no longer holds:

```text
`Board.add` (Board.Valid.preserved_add) leaves:
  case isTrue.refl.bounded
  c1 : b.items.length ≤ 100
  ⊢ (b.items ++ [t]).length ≤ 100
```

No test had to think of the 101st item.

The same machinery covers the games. **Every stored game is valid** and **game ids are unique**, in every state the database can reach. The database won't store a game unless it comes with evidence that it is valid, and the domain's `preserves` theorems supply that evidence for every move. So no runtime check is needed, and none can be forgotten.

## From the proof to the running service

All of this is about `gamesApi`, the API as written. The step that makes it about production:

<!-- check: signature LeanApi.DbApi.serve_eq_step -->
```lean
theorem DbApi.serve_eq_step (api : DbApi s) (hexec : ExecutesAsMeaning s)
    (hwf : st.WF) (hdone : Completes api env r st) :
    api.served env r st = api.step env r st
```

In words: when a request completes, the running service (SQLite, through LeanDB) answers and changes the database exactly as `gamesApi.step` says. Every theorem above is therefore a theorem about the service you deploy.

It assumes one thing, `ExecutesAsMeaning`: that LeanDB runs each query and write as its meaning says. It is not proved, because it is about SQLite. LeanDB checks it once for everyone, by running random queries and writes against SQLite and against their meaning, and comparing. It is written as a hypothesis, so it can't be forgotten.

`hwf` says the database is well-formed: every row decodes and satisfies its rules. That isn't an assumption either. It holds of every state the service can reach, because every write keeps it.

## What exactly is proved

I want to be precise here, because a proof is only as good as its statement.

- **Proved:** isolation, restricted reads, existence privacy, availability, safe reads, retry safety, valid games, unique ids, about `gamesApi` itself, with no `sorry` and no axioms beyond Lean's standard three.
- **Assumed, and checked by testing:** that LeanDB executes queries and writes as their meaning says, on SQLite.
- **Trusted:** SQLite itself, the HTTP parser, the crypto library, and the middleware in front of the API (logging, rate limits).
- **Out of scope:** timing. And the "view" is spelled out: it includes the next game id, so a new game's id reveals how many games exist. That release is written into the theorem rather than hidden.

Every claim is listed in [EVIDENCE.md](../../EVIDENCE.md) as **proved**, **checked**, **assumed** or **open**. The table is generated from a registry of theorems, and the build refuses to call a claim "proved" if its theorem uses `sorry` or an extra axiom.

## Why bother

No amount of testing can tell you a bug *isn't* there. Tests show the cases you imagined. As an application grows, the cases you didn't imagine grow faster, and bugs remain.

A proof covers every request and every database state at once. Lean lets us write the API, the domain and the queries in one language, prove things across all three, and carry the proofs to the running service. That brings us closer to a future with no bugs.

LeanAPI is at [github.com/theoriclabs/leanapi](https://github.com/theoriclabs/leanapi). It's experimental and APIs will change. I'd love to hear what you'd want to prove about your own backend.
