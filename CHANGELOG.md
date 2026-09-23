# Changelog

## 0.4.0 (M6): proofs

- Reference model `PrivateGames.Model.step : Req → World → Res × World` over
  the exported proved routes, sharing `decode` and `core` with the native
  service; route resolution shared through `Router.resolveIn`.
- Theorems: `step_noninterference` (single-request response noninterference
  over the full response), `existence_private`, `keyed_replay`, `reads_pure`,
  `unrouted_pure`, `resign_state_idem`, `read_available`. All 31 audited
  theorems in CI.
- Differential test: native service ≡ model on random request sequences
  (mutation-checked).
- `EVIDENCE.md`; decisions 0009 (Q4), 0010 (Q6), 0011 (Q11).

## 0.3.0 (M4, M5): domain-first endpoints

- `examples/private-games`: domain, LeanDB persistence (codecs from smart
  constructors with round-trip proofs, re-validating reconstruction, scoped
  reads with the policy in the SQL predicate, compare-and-swap commits with
  authority re-checked under the write lock, retry receipts in the same
  transaction, single writer plus reader pool), operations bound to routes
  (`If-Match` → expected revision, `ETag` from the revision,
  `Idempotency-Key`), runnable server, seed script and Dockerfile.
- HTTP tests for every DESIGN §9.3 case.
- Decisions 0008 (Q5) and 0012 (Q7).
- LeanDB `v0.4.0` pinned by git tag.

## 0.2.0 (M2): JWT and password auth

- Depends on leancrypto 0.1.0 (OpenSSL 3 FFI; decision 0002).
- `LeanApi.Jwt`: HS256 verification (`exp`, `nbf`, `iat`, `iss`, `aud`,
  leeway, `maxAge`), rejects `alg: none`, other algorithms and `crit`,
  constant-time signature compare, keys under 32 bytes refused; `Jwt.sign`;
  `jwtBearer` authenticator mapping claims to an actor.
- `LeanApi.Tokens`: opaque 256-bit tokens stored and looked up by SHA-256
  digest only.
- `hashPassword` / `verifyPassword` (scrypt), `basicWithPasswords` with dummy
  verification for unknown users.
- Decision 0004 (Q9): mechanisms in LeanAPI, accounts in the app.

## 0.1.0 (M1): HTTP toolkit

- Routing: method + path templates (`{id}`, `{id:int}`, `{id:nat}`, `{*rest}`),
  groups and prefixes, precedence by segment kind, conflict detection at
  `Router.build` and at elaboration time (`routes!`). 404 vs 405 with `Allow`,
  automatic `HEAD` and `OPTIONS`, trailing-slash policy (redirect / strict /
  ignore), dot segments refused.
- Extraction: typed path, query, header, cookie, JSON and form extractors;
  `FromParam` / `FromBody` / `SmartCtor` so domain constructors validate at
  the boundary; errors with field locations (`body.title`, `query.page`),
  accumulated across fields; 415 and 406.
- Per-route body limits enforced while streaming (413).
- Responses: builders for text, JSON, bytes, redirects, `Set-Cookie`;
  RFC 9457 `application/problem+json` errors; exceptions become a 500
  without internal details, logged under the request id.
- Middleware: `App → App`, ordered named stacks with `Stack.describe`;
  built-ins `recover`, `requestId`, `accessLog`, `cors`, `trustedProxy`,
  `timeout`, `health`, `securityHeaders`.
- Authentication interface: `Authenticator`, bearer / Basic / session cookie
  over app-supplied verifiers, `orElse`, `requireAuth`, `optionalAuth`, 401
  with `WWW-Authenticate`.
- Runtime: `serve` with graceful shutdown on SIGTERM/SIGINT; handlers run on
  dedicated threads; `Worker`/`Pool` bounded queues for blocking work.
- In-process test transport over `Std.Http.Server.serveConnection`.
- `examples/notes`.
