# Changelog

## Unreleased: typed endpoints (docs/ENDPOINTS.md)

- **`LeanApi.Http.Endpoint`.** An endpoint is a function whose type is its
  specification:
  - inputs are parameters typed by source (`Auth`, `Path`, `Query`, `Body`,
    `Header`, `IfMatch`, `FreshToken`; open class `FromRequest`);
  - the effect is `Reads σ` / `Writes σ` (pure, run atomically against a
    pluggable `Store σ`), `IO`, or none;
  - success shapes are `ToResponse` (`Created`, `Versioned`, `Paged`,
    `NoContent`, `WithCookie`, JSON);
  - failures are `Except ε` with `ToProblem ε`, whose status is typed as
    4xx/5xx.
- **Compile-time checks.**
  - `GET` and `HEAD` endpoints carry a proof that their effect is safe.
  - `api!` checks path arity against templates and route conflicts, and
    records each signature for `Api.describe`.
- **Error handling.** Invalid fields are reported across all parameters in
  one 422.
- **Authentication.** `Authenticates σ α` names schemes by actor type, with
  `sessions` and `passwords` helpers over pure state lookups.
- **Notes rewritten** on typed endpoints. Its test suite passes unchanged.
- **Pure meaning, and laws as proofs.**
  - Every typed endpoint means `Env → Req → σ → Res × σ`. Randomness and time are in `Env`; authentication is pure (`sessions`, `passwords`, `jwt`). The runtime runs each request atomically.
  - `Api.toSys` makes a typed API a `Props.Sys`.
  - `Handler` proves its own laws (safe handlers never write; `Preserved I` makes a handler preserve `I`).
  - For every typed API: `Api.step_safe` (GET/HEAD never change state) and `Api.inductive_of` (per-endpoint obligations give an invariant).
- **Inputs.** Optional headers (`Header n (Option α)`), `IfMatchRequired` (428), `Now`.
- **Problems.** `ToProblem.extensions` for problem members.
- **Isolation for typed APIs.** `Handler` computes an `Isolated` obligation from the signature, where `Auth` narrows the relation to the actor's view (`ViewOf σ α`). `Api.noninterference` proves, for every typed API, that a request authenticated as `p` gets a response depending only on `p`'s view. private-games: `api_noninterference` and `api_existence_private` on the typed API.
- **private-games on typed endpoints.** `PrivateGames/Api.lean` has typed signatures, responses and errors. `api_allValid`, `api_uniqueIds` and `api_freshIds` are proved on it through `Api.inductive_of`, and GET safety is free. The differential test is now three-way (native, reference model, typed API), with mutations exercising every error status.

## Unreleased: review fixes (docs/reviews/2026-09-23-review-eb67460.md)

- **`allValid` rests on the domain** (H1). The store of games runs the
  domain decisions (`openGame`, `decide`), so every stored game is `Valid`
  because of the `preserves`-generated theorems, not the commit's runtime
  check.
- **`NIPackage` cannot be vacuous** (H2). It requires, per observer, a
  hiddenness witness with an acting request, an availability companion tied
  to `acts`, and a refusal. `gamesNI` discharges them with one checked
  assumption (`ReadPlumbing`).
- **`#check_invariant` checks every initial world** (H3) and never reports
  "inductive" when one violates the invariant; messages state the search
  depth.
- **`preserves` requires the state argument to be named when ambiguous**
  (H4): `preserves Small by setTo[s]`.
- **Registry coverage is derived** (H5). `register_invariant` requires an
  `Invariant S I` theorem and takes its covered writers from
  `HasWriters S`; `covers` is gone. Tables are declared (`declare_tables`);
  writers touch a known table or are `readonly`; `unproved` parses and is
  shown in the generated row.

## 0.6.0 (M8–M12): the property library

`LeanApi.Props` (docs/PROPERTIES.md). All theorems below are in
`scripts/audited_theorems.txt` (127 theorems, no `sorry`, no extra axioms).

- **Kernel (M8).** `Sys`, `Reachable`, `Invariant`, `Inductive`,
  `Invariant.of_inductive`; the operator algebra with proved rules
  (conjunction and its relative form, disjunction, indexed forms with the
  frame-based local rule, pullback along a `Simulation`, union of writers);
  `Inductive.restrict`; `pre`, `WeakestInductive`, `invariant_iff`, `CTI`.
  `ListStore` lifts entity invariants to a store and proves unique ids with
  the `Fresh` strengthening. `ScopedApp.toSys` bridges existing apps
  (decision 0016).
- **private-games system invariants**, previously only runtime checks:
  every stored game is `Valid` (`allValid`) and game ids are unique
  (`uniqueIds`, with `freshIds`), in every reachable model world.
- **Authoring (M9).** `invariant` generates the `Prop`, the runtime check
  naming failing fields, `check_iff` and a `Decidable` instance;
  `proof_only` fields; `preserves` generates one theorem per decision and
  proves the routine cases with `invariant_cases`, printing the rest by
  field. `StoredInvariant` makes the storage check the generated one
  (decision 0017). private-games `Valid` migrated; `validB`, `resignedOk`,
  `validB_iff` removed. README examples are compiled in CI.
- **Check before proving (M10).** `Enumerate` with a deriving handler that
  supports proof fields; `#check_invariant` (vacuity, counterexamples to
  induction with reachability, `I ∧ pre I`, a `List` representation
  warning); hiddenness witnesses (`checkHidden`). Plausible was evaluated
  and not adopted (decision 0018).
- **Registry and evidence (M11).** `register_property`,
  `register_invariant`, `declare_writer`, `#properties`,
  `#evidence_tables`, `#check_writer_coverage`. A proved claim is refused
  unless its theorems pass the axiom rule. EVIDENCE.md's claim tables are
  generated (`scripts/gen_evidence.sh`, `--check` in CI).
- **Other shapes (M12).** `Safe` (discharged from the plan type by
  `ScopedApp.safe_of_pure_plans`), `StepProp`/`Monotone`/`Frame` with the
  transition-augmented system, `Enabled`, `Observation`/`NI`/`Hidden`/
  `NIPackage`, trace NI by unwinding, and the `Keyed` transformer with
  `LedgerLaws`. private-games: move logs only grow (`movesGrow`); one
  caller's successor view is preserved (`step_view_caller`); trace
  noninterference for a coalition (`trace_noninterference`); keyed replay
  after any interleaving, for the model's own receipts
  (`keyed_replay_after`) and for the generic `Keyed` wrapper
  (`gamesKeyed_replay_after`); key-reuse refusal for the wrapper
  (`gamesKeyed_reuse`). Decision 0019.

## 0.5.0 (M7): generalize

- `LeanApi.Proofs.ScopedApp`: reusable response noninterference for one
  authenticated caller's view after three caller-view obligations. The
  stronger all-views theorem also preserves successor views. Both forms are
  instantiated by private-games and `Notes.Shared` (notes with sharing).
- Typed middleware stages (`guard`, `decorate`) with proved contracts
  (decision 0013).
- OpenAPI 3.1 generation from route metadata, `/openapi.json` and `/docs`,
  and `x-leanapi-proved` markers; `Router.coverage` reports routes outside
  the proved set.
- Conditional requests (`If-None-Match` → 304 for reads, pre-write
  `checkIfNoneMatch` → 412, `If-Match` → 412/428,
  `If-Modified-Since`), token-bucket rate limiting (429 + `Retry-After`),
  Server-Sent Events formatting, W3C `traceparent` tracing, buffered
  `multipart/form-data`, `cacheControl`/`vary` helpers.
- Decision 0014 proposes 1.0 criteria (Q12).

## 0.4.0 (M6): proofs

- Reference model `PrivateGames.Model.step : Req → World → Res × World` over
  the exported proved routes, sharing `decode` and `core` with the native
  service; route resolution shared through `Router.resolveIn`.
- Theorems: `step_noninterference_caller` (single-request response
  noninterference for one authenticated player's view), `existence_private`,
  `keyed_replay` (immediate replay after a successful fresh keyed write),
  `reads_pure`, `unrouted_pure`, `resign_state_idem`, `read_available`.
  Theorems are checked by the local axiom-audit script; CI execution is
  separately tracked in [EVIDENCE.md](EVIDENCE.md).
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
