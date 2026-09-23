# LeanAPI

**A web framework for Lean 4 where your API's guarantees are theorems.**

LeanAPI gives you what you expect from Express or FastAPI: routing, typed request extraction, validation, middleware, authentication, OpenAPI. It is also built so you can **prove** properties of the running service, across the HTTP boundary, your domain logic and the database ([LeanDB](https://github.com/theoriclabs/LeanDB)). For example:

- *No route ever returns another user's data*, including through status codes, error messages or counts.
- *Retrying a request with the same idempotency key never applies it twice.*
- *Every accepted command keeps the domain valid.*

Tests can show a bug is present. A proof shows a whole class of bugs is absent, for every request and every state. LeanAPI is a framework for writing services where that is practical.

> **Status: 0.5.0, experimental.** The toolkit is usable, and the proved example is real. APIs will change. [EVIDENCE.md](EVIDENCE.md) lists exactly what is proved, what is only tested, and what is assumed.

---

## Hello, LeanAPI

```lean
import LeanApi
open LeanApi Lean

def routes : List Route := routes! [
  Route.get "/hello/{name}" fun req =>
    pure (Res.text s!"hello {req.param? "name" |>.getD ""}"),
  Route.get "/search" (handle ((·, ·) <$> Extract.query (α := Nat) "page" <*> Extract.queryD "q" "")
    fun (page, q) => pure (Res.text s!"page {page}, q {q}"))
]

def main : IO Unit :=
  serve (Service.ofRouter (Router.build! routes)
    (Stack.of [recover, requestId, accessLog, health, securityHeaders]))
    { port := 8080 }
```

`routes!` rejects conflicting routes (for example `/a/{x}` and `/a/{y}` on the same method) **at compile time**. A missing or malformed `page` produces a 422 in RFC 9457 `problem+json`, naming the field.

## From a domain rule to a proof

The core idea: write the domain in plain Lean, state its invariant, prove that every accepted decision preserves it, and expose the decision over HTTP. The HTTP layer decodes input through the same constructors the domain uses, so invalid data never reaches the decision.

```lean
import LeanApi
open LeanApi LeanApi.Props Lean

-- 1. Values carry their rules. The only way to get a `Title` is `Title.make`.
structure Title where
  raw : String
  deriving ToJson

instance : SmartCtor Title String where
  make s := if s.trimAscii.isEmpty then .error "title must be nonempty" else .ok ⟨s⟩
  raw := (·.raw)

-- 2. State, and the invariant it must keep. `invariant` also generates the
--    runtime check `Board.Valid.check` (naming failing fields), a
--    `Decidable` instance, and a proof that the check matches the `Prop`.
structure Board where
  items : List Title
  deriving ToJson

invariant Board.Valid (b : Board) where
  bounded : b.items.length ≤ 100

-- 3. A decision: pure, and allowed to refuse.
def Board.add (t : Title) (b : Board) : Except String Board :=
  if b.items.length < 100 then .ok { items := b.items ++ [t] } else .error "board is full"

-- 4. The proof that every accepted decision keeps the invariant. `preserves`
--    generates `Board.Valid.preserved_add` and proves it: refusals close
--    themselves, and the accepted branch is arithmetic.
preserves Board.Valid by Board.add

-- 5. Expose it. `Extract.json` decodes the body through `Title.make`.
def routes (board : IO.Ref Board) : List Route := routes! [
  Route.post "/items" (handleJson (Extract.json (α := Title)) fun t => do
    match (← board.get).add t with
    | .ok b => board.set b; pure (Res.created (toJson b))
    | .error why => pure (Problem.conflict why).toRes)
]
```

`POST /items` with `{"title": ""}` → **422**, rejected at the boundary by `Title.make`. The 101st item → **409** `board is full`. The generated theorem guarantees that no sequence of successful requests can produce a board that breaks `Valid`. When `preserves` cannot close an obligation by itself, it fails and prints each remaining goal, tagged with the field and the branch conditions, and you add `| Board.add => tactic` for just that goal.

This example proves a property of *one decision*. The next section shows properties of the *whole API*.

## Whole-API guarantees: the private-games example

[`examples/private-games`](examples/private-games/README.md) is a LeanDB-backed service of private tic-tac-toe games. Only a game's two players may see or play it. It has authentication, revision-checked moves (`ETag` / `If-Match`) and idempotency keys. The same decision code runs in the native server and in a reference model, and Lean proves the following about the model:

| Guarantee | Theorem |
|---|---|
| **Isolation.** For a request authenticated as player `p`, the complete response (status, every header, body bytes) depends only on `p`'s view. Other players' games may differ arbitrarily | `step_noninterference_caller` |
| **Existence privacy.** A game you're not in is indistinguishable from a game that doesn't exist | `existence_private` |
| **Keyed idempotence.** Replaying a committed keyed request returns the recorded response and changes nothing | `keyed_replay` |
| **Safe reads.** `GET` routes, and unrouted requests (404, 405, OPTIONS), never change state | `reads_pure`, `unrouted_pure` |
| **Domain.** Accepted moves are allowed, follow the transition rules and keep every game valid | `decide_allowed`, `decide_transition`, `decide_valid` |
| **Availability.** A player can always read their own game (so "reject everyone" doesn't count as secure) | `read_available` |

The precise scopes (what "view" includes, what is only checked by tests, and the trusted base: `Std.Http`, SQLite, crypto, middleware, and model ≡ native) are in [EVIDENCE.md](EVIDENCE.md). Every listed theorem is checked by `./scripts/axiom_audit.sh`: no `sorry`, no `native_decide`, no extra axioms.

### Reusing the isolation proof

Isolation doesn't have to be re-proved per app. Describe your service as a `LeanApi.Proofs.ScopedApp`:

```
route → authenticate → decode → load (scoped to the caller) → core → commit
```

Then prove three small facts about your storage model: authentication, the scoped load and the commit's response depend only on the caller's view. You get `step_noninterference_caller` for every route. `decode` and `core`, your actual business logic, need **no** proof. Both private-games and a second app with sharing (`examples/notes`, `Notes/Shared.lean`) are instances.

## Invariants and properties

Today you state invariants as ordinary Lean propositions and prove them preserved, as in the `Board` example above and in private-games' [`Domain/Game.lean`](examples/private-games/PrivateGames/Domain/Game.lean). This works, but it is manual:

- you write the `Prop` and a matching `Bool` check for runtime validation;
- you prove they agree;
- you prove preservation per command;
- you lift the result to "every stored game is valid" yourself.

The next milestones turn this into a library: define an invariant once and get the runtime check, the per-command obligations, the lift to the whole system, and counterexample search before you try to prove anything. The design is in [docs/PROPERTIES.md](docs/PROPERTIES.md), including how invariants compose and how to tell whether one is admissible. The implementation plan is [PLAN.md §M8–M12](PLAN.md#next-the-property-library-m8m12).

## Features

| Area | What you get |
|---|---|
| **Routing** | `{id}`, `{id:int}`, `{id:nat}`, `{*rest}`; groups; precedence literal > constrained > param > catch-all; 404 vs 405 with `Allow`; automatic `HEAD` and `OPTIONS`; trailing-slash policy; conflicting routes rejected at compile time |
| **Extraction** | Path, query, header, cookie, JSON and form bodies. `SmartCtor` plugs your domain constructors in. All errors are reported at once, with locations (`body.title`) |
| **Content** | 415 on a wrong `Content-Type`, 406 on `Accept`, per-route body limits enforced while streaming (413) |
| **Errors** | RFC 9457 `application/problem+json`. Exceptions become a 500 with no internal detail, logged under the request id |
| **Middleware** | `App → App`, named stacks with printable order: `recover`, `requestId`, `accessLog`, `cors`, `trustedProxy`, `timeout`, `health`, `securityHeaders`. Typed stages with proved contracts |
| **Auth** | `Authenticator` interface; bearer, Basic and session cookies over your verifier; `orElse`, `requireAuth`, `optionalAuth`; 401 with `WWW-Authenticate` |
| **JWT and passwords** | HS256 JWT verification (`alg: none` and algorithm confusion rejected), opaque tokens stored as SHA-256 digests, scrypt password hashes |
| **HTTP extras** | Conditional requests (304/412/428), rate limiting (429), Server-Sent Events, `traceparent`, multipart, OpenAPI 3.1 with a `/docs` page |
| **Persistence** | LeanDB integration in the example: scoped queries, compare-and-swap commits, idempotency receipts in the same transaction, single writer with read-only reader pool |
| **Testing** | In-process test client over `Std.Http.Server.serveConnection`: the real parser and writer, no sockets |
| **Proofs** | `ScopedApp` isolation theorem; axiom audit script; route coverage report listing routes outside the proved set |

## Using it in your project

In `lakefile.toml`:

```toml
[[require]]
name = "leanapi"
git = "https://github.com/theoriclabs/leanapi"
rev = "v0.5.0"
```

Requirements:
- Toolchain `leanprover/lean4:v4.33.0`.
- OpenSSL 3 (`brew install openssl@3` or `apt install libssl-dev`) for [leancrypto](https://github.com/theoriclabs/leancrypto).
- SQLite development headers if you use LeanDB.

> The `leanapi` and `leancrypto` repositories are currently private. You need read access to both.

## Build, test, audit

```bash
lake build                                                # the library
lake build leanapi_tests && ./.lake/build/bin/leanapi_tests
./scripts/axiom_audit.sh                                  # every theorem in EVIDENCE.md
lake build notes games                                    # the example servers
```

Run the examples:

```bash
./.lake/build/bin/notes 8080                              # notes: auth, ETags, CORS, pagination
./.lake/build/bin/games --port 8080 --db games.sqlite     # private-games
./examples/private-games/seed.sh http://127.0.0.1:8080
```

## Limits worth knowing

- **Throughput is modest.** LeanAPI runs on Lean's built-in `Std.Http` server (toolchain 4.33). On a 10-core laptop with `ab` and keep-alive, a trivial route serves roughly **2,000–3,500 req/s**. Bare `Std.Http` without LeanAPI is within about 10% of that, so the transport is the ceiling. The transport sits behind one module (`Runtime/Server.lean`) and can be replaced without touching routes or proofs.
- **Proofs are about a model.** The native server runs the same decision code, and a differential test compares the two, but that correspondence is *checked*, not proved.
- **What remains open** is listed in [EVIDENCE.md](EVIDENCE.md#open) and the latest [review](docs/reviews/).

## Documentation

| Document | What it covers |
|---|---|
| [DESIGN.md](DESIGN.md) | The architecture: domain first, HTTP and persistence as adapters, proof surface, open questions |
| [docs/PROPERTIES.md](docs/PROPERTIES.md) | The property library: shapes, admissibility, composing invariants |
| [PLAN.md](PLAN.md) | Milestones M0–M7 (shipped) and M8–M12 (property library) |
| [EVIDENCE.md](EVIDENCE.md) | Proved / checked / assumed / open, claim by claim |
| [docs/decisions/](docs/decisions/README.md) | Decision records for each settled design question |
| [docs/reviews/](docs/reviews/) | External reviews and follow-ups |
| [CHANGELOG.md](CHANGELOG.md) | Release notes |

## License

MIT. Copyright (c) 2026 Theoriclabs, Inc.
