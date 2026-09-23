# LeanAPI

*A FastAPI / Express alternative for Lean 4, with theorems about your whole backend.*

Over the past few days I released a handful of tools for the Lean ecosystem:

- **LeanReact**, for UIs;
- **LeanDB**, a typed database;
- **LeanHttp**, an HTTP client, two days ago.

This is the next one: **LeanAPI**, a backend framework in the spirit of FastAPI and Express.

Several people have asked me what the point is of rewriting all of this in Lean. The short answer: **you can prove properties of a program across system boundaries.**

A backend sits between two systems: the API that clients call, and the database behind it. Most bugs that hurt are in the gaps between them. A check is done in one place and forgotten in another, or data that was valid on the way in is invalid on the way out. When the API, the domain logic and the database interface are all written in Lean, you can state properties about the *whole* system and prove them.

I'll show two such properties with a small example, then how you write your own.

## It's a normal web framework first

An endpoint is a plain function, and its type tells you what the request does:

```lean
def editNote (me : Auth User) (id : Path NoteId) (rev : IfMatch Rev) (edit : Body NoteEdit) :
    Writes State (Except EditError (Versioned NoteView))
```

Read the signature:
- the caller is authenticated as a `User`;
- the note id comes from the path;
- an `If-Match` revision is taken if one is sent;
- the body is decoded (and validated) as a `NoteEdit`;
- it **changes state**;
- it answers with the note and its `ETag`, or with one of the failures listed in `EditError`.

The body is plain logic, with no request or response objects. A `GET` whose handler writes doesn't compile.

You get what you'd expect:
- routing with typed path parameters;
- JSON and form extraction, validated at the boundary;
- errors in `problem+json`;
- middleware;
- authentication with JWT, bearer tokens and username/password;
- rate limiting, CORS, conditional requests and OpenAPI.

## The example: private games

Take a table of games. Each game has two players, and the rule is simple: **only those two players can see a game.**

Here is the rule, exactly as it appears in the code:

```lean
def visible (p : PlayerId) (g : Game) : Bool := g.isParticipant p
```

There are many ways to get this wrong:

- Forget the auth check on one route.
- Check that the user is logged in, but not that the game is *theirs*. Someone who guesses or leaks a game id can then watch another person's game.
- Return **403** for someone else's game but **404** for a missing one. That tells an attacker which ids exist.
- Put another player's name into an error message.

Tests catch the cases you thought of. In Lean we can prove that **no code path** accessible through API, does any of this.

### Property 1: you only ever see your own games

This is the theorem, as it appears in the repository:

```lean
theorem step_noninterference_caller (r : Req) (p : PlayerId) {w₁ w₂ : World}
    (h : SameView p w₁ w₂) (hp : authenticate r w₁ = .ok p) :
    (step r w₁).1 = (step r w₂).1
```

In words:
1. Take any request `r` that authenticates as player `p`.
2. Take any two database states `w₁` and `w₂` that look the same to `p`: the same games visible to `p`, and the same session and player tables.
3. They may differ in anything else. Other people's games can be completely different.
4. Then the **entire HTTP response is identical**: status code, every header, every byte of the body.

So nothing `p` receives can depend on data `p` isn't allowed to see. `step` is the whole request pipeline: routing, authentication, decoding, the domain decision, the database read and the commit. So this covers every route and every branch, including 401, 404, 405, 409 and 412, not just the happy path.

Two things follow directly:
- **A guessed game id is indistinguishable from a missing one.** Both return the same 404 (`existence_private`).
- **"Deny everyone" isn't a loophole.** A separate theorem proves a player can always read their own games (`read_available`).

### Property 2: retrying a request is safe

A player makes a move and the network drops the response, so the client retries. If the server applied the move twice, the game would be corrupted.

With an `Idempotency-Key` header, LeanAPI records the outcome in the same database transaction as the move. The theorem is about what happens when the same request comes back:

```lean
step r (runReqs rs (step r w).2) = (markReplay (step r w).1, runReqs rs (step r w).2)
```

In words:
1. Run a keyed request `r` once, and let it commit.
2. Then run any sequence `rs` of other requests to the game routes, from any player.
3. Then send `r` again. You get back the recorded response, marked as a replay, and the state doesn't change.

The move is applied exactly once. Reusing the same key with a *different* body is refused (checked by the test suite).

## Writing your own properties

These two aren't special cases. Your domain rules are properties too, and LeanAPI makes them cheap to state:

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

`invariant` declares the rule. From it you also get a runtime check (which names the field that failed) and a proof that the runtime check and the rule agree. `preserves` proves that every successful `add` keeps the board valid.

Now introduce an off-by-one: change `<` to `≤`. The **build fails**, and Lean shows exactly what no longer holds:

```
`Board.add` (Board.Valid.preserved_add) leaves:
  case isTrue.refl.bounded
  c1 : b.items.length ≤ 100
  ⊢ (b.items ++ [t]).length ≤ 100
```

No test had to think of the 101st item.

The same tools scale up. In the games example, **every stored game is valid** and **game ids are unique**, in every state the system can reach. Both are proved from the domain's own rules; before, they were only checked at runtime.

## What exactly is proved

I want to be precise here, because a proof is only as good as its statement.

- **The theorems are about a reference model** of the service. It runs the *same* decision code as the real server, but reads from an in-memory world instead of SQLite. That the real server matches the model is checked by a differential test, not proved.
- **Some things are trusted, not proved:** SQLite, the HTTP parser, the crypto library, and the middleware.
- **The "view" is spelled out.** It includes the next game id, so a new game's id reveals how many games exist. That release is written into the theorem rather than hidden. Timing isn't covered.

Every claim is listed in [EVIDENCE.md](../../EVIDENCE.md) as **proved**, **checked**, **assumed** or **open**. The table is generated from a registry of theorems. The build refuses to call a claim "proved" if its theorem uses `sorry` or any axiom beyond Lean's standard three.

## Why bother

No amount of testing can tell you a bug *isn't* there. Tests show the cases you imagined. As an application grows, the cases you didn't imagine grow faster, and bugs remain.

A proof covers every request and every state at once. Lean lets us write the backend, the domain and the database interface in one language and prove things across all three. That brings us closer to a future with no bugs.

LeanAPI is at [github.com/theoriclabs/leanapi](https://github.com/theoriclabs/leanapi). It's experimental and APIs will change. I'd love to hear what you'd want to prove about your own backend.
