# LeanAPI

**An Express/FastAPI-style web framework for Lean 4.**

Routing, typed extraction and validation, middleware, and authentication,
on top of `Std.Http`. The long-term aim ([DESIGN.md](DESIGN.md)) is to
carry domain meaning across the API and the database ([LeanDB](../LeanDB))
so an application can prove properties such as "no route returns another
user's data" and "retrying this request is idempotent". The plan is in
[PLAN.md](PLAN.md).

## Example

```lean
import LeanApi
open LeanApi Lean

structure Title where raw : String

instance : SmartCtor Title String where
  make s := if s.trimAscii.isEmpty then .error "title must be nonempty" else .ok ⟨s⟩
  raw := (·.raw)

def routes : List Route := routes! [
  Route.get "/hello/{name}" fun req =>
    pure (Res.text s!"hello {req.param? "name" |>.getD ""}"),
  Route.post "/notes" (handleJson (Extract.json (α := Json)) fun j =>
    pure (Res.created j)),
  Route.get "/search" (handle ((·, ·) <$> Extract.query (α := Nat) "page" <*> Extract.queryD "q" "")
    fun (page, q) => pure (Res.text s!"page {page}, q {q}"))
]

def main : IO Unit :=
  serve (Service.ofRouter (Router.build! routes)
    (Stack.of [recover, requestId, accessLog, health, securityHeaders]))
    { port := 8080 }
```

`routes!` rejects conflicting routes (`/a/{x}` and `/a/{y}` for the same
method) at compile time.

## Features

| Area | What you get |
|---|---|
| Routing | `{id}`, `{id:int}`, `{id:nat}`, `{*rest}`; groups; precedence literal > constrained > param > catch-all; 404 vs 405 + `Allow`; auto `HEAD`, `OPTIONS`; trailing-slash policy; `..` refused |
| Extraction | path, query, header, cookie, JSON, form; `SmartCtor` plugs domain constructors in; errors carry locations (`body.title`) and are all reported at once (422) |
| Content | 415 on wrong `Content-Type`, 406 on `Accept`, per-route body limits enforced while streaming (413) |
| Errors | RFC 9457 `application/problem+json`; exceptions become a 500 with no internal detail, logged under the request id |
| Middleware | `App → App`, named stacks with printable order; `recover`, `requestId`, `accessLog`, `cors`, `trustedProxy`, `timeout`, `health`, `securityHeaders` |
| Auth | `Authenticator` interface; bearer, Basic, session cookie over your verifier; `orElse`, `requireAuth`, `optionalAuth`; 401 with `WWW-Authenticate` |
| Runtime | `serve` with graceful shutdown; handlers on dedicated threads; bounded `Worker`/`Pool` for SQLite and FFI |
| Testing | in-process client over `Std.Http.Server.serveConnection`: the real parser and writer, no socket |
| JWT and passwords (0.2) | HS256 JWT verification (`alg: none` rejected), opaque tokens stored by SHA-256 digest, scrypt Basic auth; crypto from [leancrypto](../leancrypto) (OpenSSL 3) |
| HTTP extras (0.5) | conditional requests (304/412/428), rate limiting (429), SSE, `traceparent`, multipart, OpenAPI 3.1 + `/docs` |
| Proofs (0.4, 0.5) | `ScopedApp`: prove three view obligations about your storage model, get response noninterference for every route; typed middleware stages with proved contracts; axiom audit in CI |

Middleware is trusted code: see [decision 0001](docs/decisions/0001-q8-middleware-v01.md).
What an accepted credential does and does not establish: [decision 0003](docs/decisions/0003-authenticator-contract.md).

## Paths

Path segments are percent-decoded *after* splitting, so `/files/a%2Fb`
has one segment `a/b`. Empty segments (`//`) are 400. `.` and `..` are
refused with 400, not normalized. A trailing slash redirects (308) to the
path without it for `GET`/`HEAD` when that path has a route, and is 404
otherwise. Use `Router.build routes .strict` or `.ignore` to change this.

## Build and test

```bash
lake build
lake build leanapi_tests && ./.lake/build/bin/leanapi_tests
./scripts/axiom_audit.sh
```

Toolchain: `leanprover/lean4:v4.33.0`.

## Proved example: private-games

[`examples/private-games`](examples/private-games/README.md) is a LeanDB-backed
service of private games, with Lean proofs that **no route reveals another
player's games** (including whether they exist) and that **retrying a keyed
request returns the recorded outcome without applying it twice**. What is
proved, checked and assumed is listed in [EVIDENCE.md](EVIDENCE.md).

Design questions are settled by [decision records](docs/decisions/README.md).

## Example app

`examples/notes`: registration (JSON or form), Basic login issuing a bearer
token and a cookie, per-user notes with `ETag`/`If-Match`, pagination, CORS,
and every middleware above.

```bash
lake build notes && ./.lake/build/bin/notes 8080
```

Load sanity check (Apple M-series laptop, `ab`, notes app with the full
middleware stack including access logging to stderr; not a benchmark):

| Run | Result |
|---|---|
| `ab -n 3000 -c 16` `GET /api/notes` (bearer auth, new connection per request) | 3000/3000 ok, ~2,200 req/s |
| `ab -k -n 5000 -c 32` `GET /healthz` (keep-alive) | 5000/5000 ok, ~2,600 req/s |

## License

MIT. Copyright (c) 2026 Theoriclabs, Inc.
