# LeanAPI milestone 2 handoff (wave 1)

Updated 2026-10-05 (fixes before M3 phase 5; M3 `LeanApi.Core`; waves 1 to 3, the final wave's phases A and B, apps with no accounts, the live peers; newest first). Scope: DDD-LAPI-06 bearer transport, the native half of DDD-LAPI-05
(explicit route list), the LeanAPI side of DDD-LAPI-07 (`lake exe`, no Python, no
environment variables), and the KDF-hoisting design note (decision 4). Built and tested
against the frozen peers in `domain_driven_development/runs/partiful-m2/frozen/{LeanDB,leanreact}`.
All changes are uncommitted and confined to this repository. `Review_harsh_2026-09-23.md`
is untouched (SHA-256 `e6508dbd71b41ae382a40e4fda7e666ec5cddd0b22559870e9531f84079a00f6`
before and after).

## Before M3 phase 5 (2026-10-05): fixture namespace, bare-string statuses, `Service.mjs`

Three issues LeanReact's phase 4 (`423912e`) found in LeanAPI. LeanReact was only read.

### 1. The staged post api no longer claims `Partiful.*`

- **Cause.** A Lake library claims every module under its roots and globs, in every workspace
  that requires the package, not only in its own. LeanAPI's `lean_lib Partiful` (the staged
  `partiful_v2/Domain.lean`) therefore provided `Partiful.Domain` to the app repository too,
  which requires leanreact and so leanapi, and its own `Partiful` library provides the same
  module: Lake stopped with "could not disambiguate the module".
- **Fix.** The library is `LeanApiPartifulFixture` (glob `LeanApiPartifulFixture.+`, source
  `.lake/leanapi-partiful-fixture`). `scripts/stage_partiful_api.py` stages
  `LeanApiPartifulFixture/Domain.lean` (the post's file, imports changed, nothing else) and
  `LeanApiPartifulFixture/Server.lean` (its `app%` and `main`, the root of
  `leanapi_partiful_api`, whose name is unchanged). The old staged sources stay in
  `.lake/partiful-api` (unused, nothing claims them; the `.lake` guard keeps them). Their build
  output was moved, not deleted, to `.lake/ddd-m3/leanapi-stale-partiful-build/`: `lake env`
  puts every package's build directory on `LEAN_PATH`, and a stale `Partiful/Domain.olean`
  there could still be found by a workspace that has not built its own yet. It can be removed.
- **The other libraries, checked.** What each claims, in any workspace that requires leanapi:
  - `LeanApi`, `LeanApiCore`, `LeanContract`, `LeanApiTests`, `LeanApiPartifulFixture`: LeanAPI's
    own prefixes.
  - `TestsCore.*`, `TestsNative.*`: test-scoped, but not LeanAPI-prefixed. Not renamed now:
    LeanReact's domain tests import `TestsCore.PostPart1` (`leanreact/tests/domain/PostViews.lean`
    and nine negative fixtures), and LeanReact is not edited here. A rename to
    `LeanApiTestsCore`/`LeanApiTestsNative` should land together with those imports.
  - The example apps `Notes.*`, `PrivateGames.*`, `PolicyView.*`, `Helpdesk.*`, `Billing.*`,
    `Scheduling.*` and `TeamsDemo.*`: these are app-shaped namespaces and have the same problem
    for an app of that name. No current workspace collides (LeanReact's libraries are
    `LeanReact*`, `LeanJS`, `Examples`, `Ordering`, `Cafe`, `PrivateNotes`, `NativeTickets`,
    `LeanAppNative`; the app repository's are `Partiful`, `PartifulApp`, `TicTacToe`). Not
    renamed here: the module paths appear in the teams demo's eight beat patches, its README
    and the example READMEs, and 50+ test imports. Options for later: a `LeanApiExamples.`
    prefix, or moving the examples into their own Lake package that requires leanapi, so that
    no workspace requiring leanapi sees them at all.
  - Executable roots (`Main`, `Hello`, `Items`, `Users`, `*Main`) are not claimed: Lake
    resolves imports through libraries only.

### 2. `ErrorStatus.ofTags` reads bare strings (`LeanContract/Http.lean`)

- **Cause.** Since decision 15 a payload-free domain error is the bare string `"notFound"` on
  the wire, and `ofTags` read only the tagged form (`{"tag": …}`), so such an error had no
  status (`response.unknown_domain_error`, a 500 to the caller).
- **Fix.** `Contract.Http.errorTag` reads the tag from either form, and `ofTags` uses it. A
  constructor the error schema declares but `table` does not list now gets `otherwise`, 422 by
  default, the status `describeAt` gives every domain error; a tag the schema does not declare
  still fails. `ErrorStatus.ofOperation` reads a bare string the codec rejects as the
  payload-free constructor it names, so both policies accept both forms. The generated client
  is unchanged (its `statusByTag` sees the decoded, tagged error).
- **Test.** `TestsCore/Envelope.lean` (run by `leanapi_core_tests`): the bare string taken
  from `Envelope.domainError` maps to 404 through `ofTags` and `domainStatus`, the tagged form
  to 404, an unlisted declared constructor to 422, an undeclared tag fails; `ofOperation`
  likewise.
- **For LeanReact to drop.** `leanreact/examples/lean/Examples/Tickets/Contracts.lean` defines
  `statusByTag` (lines 112 to 124), a copy of `ofTags` that also reads the bare string, and
  `PublicOperations.errorStatuses` uses it. It can return to
  `Contract.Http.ErrorStatus.ofTags ops.save [("notFound", 404), ("conflict", 409)]`.

### 3. `LeanContract/Service.mjs` is deleted

It imported `../runtime/actions.mjs` and `../adapters/leanjs-react.mjs`, which exist only in
LeanReact, so it could not load from leanapi. Its working copy is LeanReact's
`engine/adapters/contract-service.mjs`. `LeanContract/Fetch.mjs` and `Codecs.mjs` stay: they
are the generated client's runtime.

### Gates

`scripts/ddd_check.sh .lake/ddd-m3/leanapi-p4-gate.summary` (with a watchdog that would stop it
under 500 MB free; 726 MB at the start), every step exit 0: leanapi_tests 580/0, core tests
(including the new status checks), 28 rejections and the portable closure, native contract,
prepared, KDF, read, command, routes 51/0, post 37/0; counter 56, library 26, migration 35,
curl 24, partiful_v2 API 197 (built from `LeanApiPartifulFixture`); both transcripts, both
generated clients, diff check; 0 LeanReact/LeanJS/LeanApp imports, 0 generality hits.
`Review_harsh_2026-09-23.md` unchanged (SHA-256 as above).

## M3: LeanApi.Core (2026-10-05)

LeanAPI owns operations and endpoints and depends on no LeanReact (plan:
`domain_driven_development/runs/m3-layering/PLAN.md`, phase 3). It builds on LeanDB `f6288e5`
(`LeanDb.Model`, `LeanDb.Native`) and leanontology `5f54fb8`. LeanReact was only read.

### Build wiring

- **Requires.** LeanDB and leanontology are path dependencies (`../LeanDB`, `../leanontology`), and
  the git pin on leandb is gone. A pinned git require for fresh clones is DDD-LAPI-04. The
  manifest resolves LeanDB's `leansqlite` to LeanDB's own checkout
  (`../LeanDB/.lake/packages/leansqlite`), so the two workspaces share one build:
  `lake build leandb/LeanDb` from here is up to date. `leancrypto` is unchanged (git, `v0.1.0`).
- **Decision: toolchain `leanprover/lean4:v4.33.0`, not `nightly-2026-09-26`.** Path dependencies
  share oleans, so one build graph needs one toolchain, and LeanDB, leanontology, LeanReact and
  the apps are all on v4.33.0. The trade-off is that leanapi loses the nightly's lean4#15174
  fix (`Std.Http` no longer parks a thread on every socket read) until every repository moves
  to v4.36.0. The HTTP suite passes on v4.33.0 (580/0); throughput was not re-measured.
- **Targets** (`lakefile.toml`):
  - `LeanContract` and `LeanApiCore` are the portable libraries.
  - `LeanApi` has the roots `LeanApi`, `LeanApi.Core` and `LeanApi.Native`.
  - `TestsCore` with `leanapi_core_tests`, and `TestsNative` with `leanapi_native_checks`,
    `leanapi_apps` and `leanapi_counter_app`.
  - `LeanApiPartifulFixture` (named `Partiful` until the fixes before phase 5, below) and
    `leanapi_partiful_api` are the staged post api.
  - `LeanApiTests` and `leanapi_tests`.
- **Decision: rename `Tests.*` to `LeanApiTests.*`.** A `Tests` library in a dependency
  (leanontology, LeanDB) claims every `Tests.*` module, so `import Tests.X` resolved to
  `leanontology/tests/Tests/X.lean`. Only module paths changed, not namespaces.
- **The generated `.lake/ddd-common` workspace is retired.** `ddd_prepare_common.py`,
  `ddd_partiful.py`, `ddd_browser_target.py` and the milestone 1/2 check scripts are deleted;
  every gate builds in this repository's own workspace. The old directory
  (`.lake/ddd-common`, 2.3 GB) is still on disk: a guard stops this worker from deleting under
  `.lake`, so someone with the permission should remove it.
- **Tic-tac-toe** (`domain_driven_development/tictactoe/lakefile.lean`, phase 5) should drop
  `.lake/ddd-common` and require `leanapi from "../../leanapi"` (which brings LeanDB and
  leanontology as path dependencies), on toolchain v4.33.0. Its domain imports `LeanDb.Model`
  and `LeanApi.Core`; its server imports `LeanApi.Native` and declares
  `app% Name where api := api`.

### Modules

| Module | What it is |
| --- | --- |
| `LeanContract.*` (names kept) | Ported from leanreact `engine/LeanContract`. Operation contracts and codecs, transports, the HTTP envelope, call failures, channels, the browser bridge, and client generation (`LeanContract.Generate`, with its JS runtime `LeanContract/{Fetch,Codecs,Service}.mjs`). |
| `LeanApi.Publication.*` | leanreact's pre-domain `LeanApp/*`: `Application`, `Binding` (`PublicOperation`, `PublicMetadata`, `HttpBinding`), `Capability`, `Channel`, `Context`, `Module`, `Policy`, `Testing`. Renamed, because the `LeanApi` namespace already has `Policy`, `Method`, `Endpoint`, `Api` and `Auth`. No module is named `LeanApp`. |
| `LeanApi.Core.Flow` | The operation IR. `RequestF` EMBEDS LeanDB's `StorageRequest` (one constructor, `storage`, at the access of the operation kind) and adds only `now`, `hashPassword`, `verifyCredential` and `startSession`. `FlowF` adds `pure`, `bind`, `fail` (throw) and `check` (require). It also defines `Resources` (`extends StorageResources` with `auth`), `portableResources`, `portableAuth`, `Algebra`, `Flow.run`, `mapError`, `toCommand`, `capture`/`tryCatch`, `Operation`, `FlowMetadata`, `KdfStep`, `CredentialLink` and `RouteInput`. |
| `LeanApi.Core.Op` | `Op`, `ReadOp`, `Now`, `Clock.now`, `require` (scoped syntax), `MonadRequire`, `Principal`, `Op.mapError`, and the `Domain`/`Wire` instances for `Empty`. `MonadStorage` instances give `MonadLift DB (Op ε)`, `MonadLift Query (Op ε)` and `MonadLift Query (ReadOp ε)`, request by request (`Program.lift`). |
| `LeanApi.Core.Auth` | `Password.hash` (as `Ontology.Password.hash`, so `← password.hash` works), `Auth.verifyWith`, `Auth.startSession`, the `credential C.profile C.hash` command (one more `@[command_elab LeanDb.Model.Entities.entityFieldPair]` elaborator; it generates `C.credentialLink` and `C.verify`), and `deriving Principal`. |
| `LeanApi.Core.Publish` | `derive_operation f`. It uses LeanDB's `Requirements.generalize` with this layer's targets: family `portableResources`, `portableStorage ↦ r.toStorageResources`, `portableInstances.push portableAuth`. Metadata nodes come from `Requirements.storageNode?` plus this layer's requests and guards; KDF steps are read the same way. |
| `LeanApi.Core.Api` | `def api : Api := [post "/x" f, get "/y/:id" g]`, `Endpoint`, typed `api.f`. |
| `LeanApi.Core.Memory` | `LeanApi.Memory`, the in-memory runner. LeanDB's `Memory` store, with the clock, sessions and KDF counter around it. |
| `LeanApi.Native.*` | The native adapter (see below). |

`open LeanApi.Core` exports what an app writes: `Op`, `ReadOp`, `Now`, `Clock.now`, `require`,
`Principal`, `Password.hash`, `Auth.startSession`, `CredentialLink`, `Api`, `Endpoint`, `post`,
`get`, `derive_operation`, and the IR (`Flow`, `RequestF`, `Operation`, …). An app opens both
layers:

```lean
import LeanDb.Model
import LeanApi.Core
open LeanDb.Model LeanApi.Core
```

`scripts/CoreClosure.lean` checks that `LeanApi.Core` is portable: its import closure is itself,
`LeanApi.Publication`, `LeanContract`, `LeanDb.Model`, `LeanOntology` and Lean (1472 modules).

**Dropped (milestone 1).**
- The surface: `command%`, `query%`, `policy%`, `auth%`, `Account`, the library `SignedIn`/`Viewer`.
- The IR: the `create`/`change`/`remove`/`signUp`/`signIn`/`include` requests, and
  `Members`/`Policy`/`Projection`/`disclose`.
- The `app%` forms `operations :=`, `routes :=`, `pages :=` and `app := app`.
- `native_auth_entities%`/`native_auth_storage%`.
- The browser shell (`App.mjs`), the LeanJS page emission and the LeanJS audit.
- The milestone 1 Partiful app with its 399-check acceptance, the `partiful_v2` page and
  Chromium suite, and `lake exe partiful`. These go to LeanReact in phase 4; the old scripts
  are in git history.

### Native

**Decision: the adapter is folded into LeanAPI proper as `LeanApi.Native.*`** (namespace
`LeanApi.Native`; `adapters/domain` is deleted). Its imports are LeanApi's HTTP core,
`LeanApi.Core`, `LeanDb.Native` and leanontology, all in this build, so a separate package
had nothing left to isolate.

```lean
app% server where                                  -- accounts
  authentication := Member with Login              -- Login declared with `credential Login.member Login.hash`
  api := api
  migrations := [addShelf := Book.addField shelf (fill := .general)]

app% counters where                                -- no accounts
  api := api
```

- The native family is `LeanApi.Native.resources s := { toStorageResources :=
  LeanDb.Native.storageResources s, auth := Auth.Storage s _ }`.
- The algebra passes each embedded storage request to `LeanDb.Native.queryRequest` or
  `commandRequest`. A `StorageFault` becomes a typed framework failure (`storageFault`);
  `DbFault.corruption` becomes `storage.corrupt` (500).
- The session table (`native_session_entity%`) is a `deriving Entity` structure. Its revoke
  goes through LeanDB's `EntityStorage.update`.
- `app%` derives the schema inside the app's namespace, so generated instances are named after
  the app and two apps' modules can be imported together.

**Hooks LeanReact needs to serve pages on top** (phase 4):
1. `LeanApi.Native.declareApiApp appName api accounts migrationTerms ref : CommandElabM Unit`.
   It is the core of both `app%` forms. A full-stack `app% … where app := X` reads `X.api`,
   calls this (with `Accounts {profile, credential}` read off the domain's `credential`), then
   declares its own value `{ appName with pages := … }`.
2. `NativeApp.pages : Context s Profile → List PageRoute` and `PublicApp.pages : List PageRoute`,
   with `PageRoute {path, handler : Req → IO Res}`. They are served next to the api by
   `withPages`: a page that shares a GET endpoint's path shape is negotiated (`Accept:
   text/html` gets the page). A page handler gets the `Context`, so it can resolve the
   bootstrap actor with `Auth.resolve context.cookies env req context.store.live`. The CSRF
   cookie is `context.cookies.csrfName`.
3. `NativeApp.authOperations`: the operations whose flow starts a session. The browser shell
   uses them to recognize a sign-in reply, which carries `x-leanapp-auth-csrf` in cookie mode.
4. Client generation: `LeanApi.Native.emitRouteClient descriptions out` (or
   `NativeApp/PublicApp.emitClient`), with `LeanContract/{Fetch,Codecs}.mjs` as the runtime.
   `runApp s migrations emit serve args config` builds an app executable; its `emit` (run
   under `LEANAPP_EMIT_CLIENT`) is where a page layer also writes its own browser files.
5. Removed from the native config: `browserDirectory`, `--browser-dir` and
   `LEANAPP_BROWSER_DIR`. The page layer finds its own bundle.

Tested here: `RouteChecks` serves a page through the `pages` hook and negotiates it with the
GET endpoint, both in process and over curl. The generated-client acceptance emits and drives
both fixture clients.

### Tests and gates

**Ported from leanreact** (`TestsCore/`, compile-time `#guard`/`#guard_msgs`, run by
`leanapi_core_tests`):
- `PostPart1` (the post's operations, endpoints, requirements and metadata).
- `PostPart1Run`: in memory, generic bodies under a witness-checking family, auth, the join,
  `Changes`, the cascade.
- `Loans` and `LoansRun`.
- `Contracts`/`ContractsRun` (the ontology contract fixtures).
- `Envelope`.

Two expectations changed because `LeanOntology.Scalars` gives `Ref T` (= `EntityId T`) its
public wire (default scope only): the scoped-reference checks now name the scoped codec
explicitly.

**Rejections** (`scripts/check_core_fixtures.py`, 28): 20 in `fixtures/core`, among them the
op-level fixtures from leanreact and the seven contract rejections; 8 in `fixtures/native`,
among them `PublicSignedIn`, `UndeclaredCredential` and `SessionWire`.

**Native fixtures** (`TestsNative/`):
- `CounterApp`, `LibraryApp`, `Evolving` and `PartifulBefore` are ported to the new surface.
- `RouteChecks` is rewritten on plain operations with an authored credential.
- `NativeChecks` is new: native reads and commands on the new IR.
- `AuthChecks`, `ContractFixture` and `PostApp` are ported.

**The post's api without pages** comes from `scripts/stage_partiful_api.py`. It copies
`partiful_v2/Domain.lean` unchanged except for its two import/open lines. The staged Main
serves it with `authentication := Person with Credential`, `api := api` and the `guestList`
migration (`unmigrated` drops the migration). `scripts/ddd_partiful_api_acceptance.mjs` runs
197 checks: auth, host, RSVP, the visibility × role matrix, edit, reschedule, cancel,
restart, and the migration gate on a real pre-`guestList` database. That is the phase 2
suite's 228 checks without the 27 Chromium checks and the 4 page checks.

All gates run from `scripts/ddd_check.sh`.

## Live peers (2026-10-04): leanreact `1a25ecf`, LeanDB `08fd160`

`.lake/ddd-common` now builds from the live, committed checkouts `/Users/harshwork/code/leanreact`
and `/Users/harshwork/code/LeanDB` (`scripts/ddd_partiful.py /Users/harshwork/code/LeanDB
/Users/harshwork/code/leanreact …`), not `frozen-w2`. The lakefile has no frozen reference. The
peers are only read. Gate script and logs: `.lake/ddd-m2-scratch/leanapi-live-*`.

- **No breakage.** leanapi compiled unchanged against `represent … checked` and LeanDB's
  one-column structured values.
- **Corrupt stored values** now have a stable public code. `faultCode` maps
  `DbFault.corruption` to `storage.corrupt` (500), `locking` to `database.busy` (503) and
  anything else to `database.unavailable`. A plain route answers `{"error":"internal"}` with
  `x-leanapp-error: storage.corrupt`, and the Contract envelope carries the same code. KDF
  preparation reads report `storage.corrupt` too. The fault's message (table, column, reason)
  is never sent, and the server keeps serving.
- **Fixture.** `tests/CounterApp.lean` gains `Reservations`: a private-constructor `Slot`
  with `represent Slot as Nat × Nat by Slot.toPair checked Slot.check`, stored as one JSON
  column and served by `app% reservations where api := Reservations.api`.
  `scripts/ddd_counter_acceptance.mjs` (now 56 checks) covers:
  - the round trip, and a rejected input value as a 400 `request.decode`;
  - `[10,9]` and `not json` written straight into SQLite, both a 500 `storage.corrupt` for
    a GET and for a command, with nothing changed;
  - healthy rows still read and write afterwards.
- **Results** (`leanapi-live-gates.summary`; every gate exit 0):

  | Gate | Result |
  | --- | --- |
  | App / common build on the live peers | PASS / PASS |
  | `leanapi_tests` / route checks / `domain_post_app` | 580/0, 50/0, 37/0 |
  | Counter + reservations acceptance | 56 |
  | `partiful_v2` / milestone 1 acceptance | 228 / 399 |
  | `ddd_check_domain.sh` / `ddd_check_partiful.sh` | PASS / PASS (8 rejections) |
  | curl / migration / library / transcripts | 24 / 35 / 41 / 6 and 6 |
  | `lake exe partiful`, generated client ×2, LeanJS audit | PASS, 9 and 9, PASS |
  | `git diff --check`, generality grep, protected file | clean, 0 hits, unchanged |

## API apps with no accounts (2026-10-04)

`app% Name where api := api` (with optional `migrations := […]`) serves a portable `Api` with
no credential, no sessions and no pages. Built against `frozen-w2/leanreact-cp4` and
`frozen-w2/LeanDB-cp3`. Gate script and logs: `.lake/ddd-m2-scratch/leanapi-noacct-*`.

- **Design: a separate `PublicApp s`, with no profile type.** `NativeApp s Profile` and
  `Context s Profile` need a profile entity and an `Auth.Storage` over credential and session
  tables. An `Option` inside them would still need some `Profile` type, which would be a
  fabricated entity. `PublicApp s` holds only `build`, `descriptions` and `migrations`.
  - It shares `routerService`, `gateDatabase`, `runApp` and `emitRouteClient` with
    `NativeApp`, which now delegates to them, so its behaviour is unchanged.
  - Its operations are published by `assemblePublicCommandAt`/`assemblePublicQueryAt`. The
    actor is `()`, no Origin check is made, and presented credentials are ignored.
- **Schema.** The domain entities of the api's namespace (the root namespace for a root
  `api`) go to `native_schema%`. No session entity is added, so the database has no account
  tables; the counter acceptance checks this.
- **No actors.** An endpoint whose `f.Actor` is not `Unit` (`SignedIn`, `Option SignedIn`)
  is an elaboration error at `api := …`. It names the operation and points to `credential`
  plus `app :=` or `authentication :=`. Negative fixture: `tests/negative/PublicSignedIn.lean`.
  An operation whose flow hashes, verifies or starts a session is refused when the app is
  assembled, at startup (`app.accounts_required`).
- **Credentials, Origin and CSRF.** See the note under decision 9 (wave 1.5): no Origin or
  CSRF check, and presented credentials are ignored.
- **Fixture** `tests/CounterApp.lean` (`domain_counter_app v1|v2|v2-unmigrated`): public
  named counters with `constraint Counter.uniqueName`, `newCounter` (POST, `nameTaken`),
  `increment` (POST, `notFound`), `getCounter` (`ReadOp`, GET), and the migration `addStep`.
  The current domain sits at the root namespace. `scripts/ddd_counter_acceptance.mjs` (39
  checks, real curl and SQLite) covers:
  - the `{"ok"}`/`{"error"}` bodies and the 400 for an undecodable body;
  - POST with no Origin, and ignored `Authorization` and cookie headers;
  - no account tables, and no sign-up route;
  - the refusal without the migration, the backfill with it, and restart persistence.
- **Results** (`leanapi-noacct-gates.summary`, 23:10 to 23:14; every gate exit 0):

  | Gate | Result |
  | --- | --- |
  | App build and staged files identical / common build | PASS / PASS |
  | `leanapi_tests` / route checks / `domain_post_app` | 580/0, 50/0, 37/0 |
  | **No-accounts counter acceptance** | **39** |
  | `partiful_v2` acceptance / milestone 1 acceptance | 228 / 399 |
  | `lake exe partiful` | PASS |
  | `ddd_check_domain.sh` / `ddd_check_partiful.sh` | PASS / PASS (8 rejections, incl. `PublicSignedIn`) |
  | curl / migration / library / transcripts | 24 / 35 / 41 / 6 and 6 |
  | generated client ×2 / LeanJS audit | 9 and 9 / PASS |
  | `git diff --check`, generality grep, protected file | clean, 0 hits, unchanged |

## Final wave, phase B (2026-10-02): the post's app, served from its `App`

`partiful_v2/{Domain,Views,Main}.lean` is staged unchanged as `Partiful.{Domain,Views,Main}`
(the gate `cmp`s all three) and built natively against `frozen-w2/LeanDB-cp3` and
`frozen-w2/leanreact-cp4`. Gate script and logs: `.lake/ddd-m2-scratch/leanapi-pb-*`.

- **`app% NAME where app := X`** (`App.lean`, new syntax `domainReactApp`). `X : App`
  must be `{ api := A, pages := … }` with `A` a declared `def … : Api`.
  - The `api` is routed exactly like `api := A`.
  - The pages become the HTML routes. A navigation (`Accept: text/html`) gets the page where
    a GET endpoint shares the path.
  - The browser entry mounts the compiled `App.component` (`NAME.browserApp`, with
    `LeanApi.Domain.Browser.shellProps`/`appProps`). `pages.json` gains `app`.
  - The page title is the root of the `App`'s module (`Partiful`).
- **Authentication comes from the domain.** The credential is the one entity next to the
  `api` with a `credential C.profile C.hash` declaration, and its `Ref P` field gives the
  profile. Zero or several are errors. The browser treats an operation as signing in when its
  flow starts a session (`metadata.establishesSession`), so `authentication :=` is not needed.
  Milestone 1 `app%` and the `authentication := P with C` form are unchanged.
- **Browser shell** (`browser/App.mjs`, `mountDomainApp`): route-client CSRF on every
  non-GET, a per-call auth capture (`x-leanapp-auth-csrf`), the actor as the profile
  reference's text, a cookie poll that turns sign-out into a new auth generation, and the
  shared failure channel.
- **Staging** (`scripts/ddd_partiful.py`): `partiful_v2/` builds `partiful` (rooted at a
  launcher importing `Partiful.Main`, `needs` the bundle), `partiful_server` (rooted at
  `Partiful.Main`, run by the bundle target) and `partiful_unmigrated` (Main without its
  `migrations`, for the refusal test). Milestone 1's `partiful/` gets its own slot,
  `partiful_m1` (modules renamed `PartifulM1.*`; only its `import Partiful.` lines change),
  with its own bundle (`Partiful.app`). The browser target generator is shared
  (`scripts/ddd_browser_target.py`).
- **Old database fixture** (`tests/PartifulBefore.lean`, `domain_migration_checks
  partiful-before`): the app before `guestList`, with the same tables.
- **Generality**: `LibraryApp` (v2) is now `app% LibraryApp where app := Library.Web.app`,
  with join, add-book and book pages. Its acceptance adds HTML and Chromium checks.
- **Acceptance** (`scripts/ddd_partiful_v2_acceptance.mjs`, 228 checks): auth (cookie, bearer,
  token; unknown email = wrong password), host, RSVP (idempotent, the cutoff on the server
  clock), the visibility × role matrix, edit via `Party.Changes`, all four reschedule errors,
  the cancel cascade, restart, the migration gate on a real old database, and Chromium.
  Transcript: `runs/partiful-m2/post-transcript.txt` (also `docs/ddd-m2-partiful-transcript.txt`).
- **`lake exe partiful`** (`scripts/ddd_lake_exe_partiful.sh`): an empty environment
  (`env -i`), no Python step, ready on 127.0.0.1:8080, serving the pages, the bundle and the API.
- **First gate run, two failures, both fixed.**
  - `partiful_m1_acceptance`: the Mac went into clamshell sleep (pmset, 12:08:22, 299 s) just
    after the server was spawned. On wake the wall-clock 15 s deadline had passed. Readiness
    deadlines now use `performance.now()` (awake time), and a timeout prints the server log.
    The binary and port were fine: the rerun passes 399.
  - `check_partiful`: the negative fixture `AuthStoreWire` still imported `PartifulMain`, the
    old module name. Its stale olean clashed with the new `Partiful.Domain`, and the
    error-count `test` failed under `set -e` without a message. The fixture now imports
    `PartifulM1Main`. The script traps `ERR` and names the step, the line and the command, and
    a mismatched fixture prints its log.
- **Results** (rerun, 19:50 to 19:53, `leanapi-pb-gates.summary`; every gate exit 0, no
  system sleep during the run):

  | Gate | Result |
  | --- | --- |
  | App build (`partiful`, `partiful_unmigrated`, `partiful_m1`) and staged files identical | PASS |
  | Common build | PASS |
  | `leanapi_tests` / route checks / `domain_post_app` | 580/0, 50/0, 37/0 |
  | `partiful_v2` acceptance | 228 |
  | `partiful_v2` transcript | 6 |
  | Milestone 1 Partiful acceptance (`partiful_m1`) | 399 |
  | `lake exe partiful` (empty environment, port 8080) | PASS |
  | `ddd_check_domain.sh` / `ddd_check_partiful.sh` | PASS / PASS (7 rejections, axioms incl. `server`) |
  | curl / migration / post transcript / library | 24 / 35 / 6 / 41 |
  | generated client (post, library) / LeanJS audit | 9 and 9 / PASS |
  | `git diff --check`, generality grep, protected file | clean, 0 hits, unchanged |

## Final wave, phase A (2026-10-02): the final peers

Built in place against `frozen-w2/leanreact-cp4` and `frozen-w2/LeanDB-cp3`.
Gate script and logs: `.lake/ddd-m2-scratch/leanapi-w4-*`.

- **Credentials are explicit.** `native_credential_storage%` (and so
  `authentication := P with C`) reads the profile and hash field names off the declared
  `C.credentialLink` (from `credential C.profile C.hash`). Nothing is taken from the
  structure's shape. Verification reads `CredentialLink.profile`, the new name for `person`.
- **Fixtures use the portable declarations.**
  - `PostApp` drops `cascade%`; the post declares `constraint Rsvp.cancelWithParty : cascade party`.
    `cancel` is served, and its cascade is checked: the RSVPs go, the people stay.
  - `LibraryApp` declares `credential`, `link Loan.book Loan.member` and
    `constraint Loan.removeWithBook : cascade book`.
  - `api.f.endpoint` constants are read unchanged by `apiEndpoints`.
- **Wire.** Payload-free constructors are bare strings (`"everyone"`, `"hidden"`, domain errors
  in the Contract envelope too), and `Nat`/`Int` are bare numbers (`{"ok":1}`). The decoders still
  accept the old forms. Tests, the acceptances and both transcripts were updated.
- **Generality.** The audit
  `grep -rniEw "partiful|party|parties|rsvps?|persons?|people|guests?|attendees?|guestlist"` over
  `LeanApiDomain`, the browser shell, the README and the lakefile finds 0 hits.
- **Milestone 1 client test** (`tests/client.test.mjs`) reads the recorded bytes with the
  client's exact `parseJson`, and tampers with `hidden` in its old object form.
- **Results** (`leanapi-w4-gates.summary`):

  | Gate | Result |
  | --- | --- |
  | App / common build | 324 / 501 jobs |
  | `leanapi_tests` | 580/0 |
  | route checks | 50/0 |
  | `domain_post_app` | 37/0 |
  | `ddd_check_domain.sh` | PASS, client 5/0, on the rerun after the client-test port; the first run failed 2 tests on the new number and string forms |
  | `ddd_check_partiful.sh` | PASS, 7 rejections |
  | Partiful acceptance | 399 |
  | curl acceptance | 24 |
  | migration acceptance | 35 |
  | post transcript | 6, regenerated in `docs/ddd-m2-post-transcript.txt` with `"guestList":"everyone"` |
  | library acceptance | 26 |
  | generated client | 9/9 each |
  | LeanJS audit | 13/0 |
  | `git diff --check` | clean |

  The protected file is unchanged.

## Wave 3 (2026-10-02): authored auth, KDF hoisting, the new envelope

Built in place against `frozen-w2/leanreact-cp2` and `frozen-w2/LeanDB-cp2`.
Gate script and logs: `.lake/ddd-m2-scratch/leanapi-w3-*`.

### KDF hoisting (design D, implemented)

- **Algebra.** `hashPassword`, `verifyCredential` and `startSession` get native cases in
  `Native.commandRequest`, which now takes an `Auth.Preparation`. `linkField` lowers to
  `LinkEvidence.project` in reads, writes and the probe.
- **When it applies.** `assembleCommandAt` checks the operation's metadata. If `kdf` is
  nonempty or `establishesSession` is set, the operation takes `assembleAuthoredAt`
  (`preparedCommandAt` with `prepareAuthored`).
- **`.hash f`.** Scrypt runs on input field `f`.
- **`.verify f`.** The flow's read prefix runs in a read snapshot through a probe algebra
  (`Flow.run` over `ExceptT Probe (Read s)`). It stops at `verifyCredential` with the
  profile key and the stored hash, read with `EntityStorage.select` filtered by
  `link.person`; there is no index on it yet. Verification runs there, against the dummy
  hash when no profile was found.
- **Gate.** All of that runs under `KDFGate`. A refused Origin or credential costs no KDF.
- **In the transaction.**
  - A presented session is rotated.
  - `hashPassword` is answered from the preparation.
  - `verifyCredential` accepts only the prepared verdict for the same profile, password and
    live stored hash.
  - `startSession` inserts the prepared session row.
  - After commit the reply carries a cookie, or in token mode `{"ok":{"profile":n,"token":…}}`.
- **New pieces.**
  - `Auth.Preparation`, `Auth.Verified`, `Storage.startSession`, `Storage.started`, and
    `Storage.checksCredential`. An authored credential has no version or enabled flag.
  - `KDFGate.runs`, an optional completion counter.
- **Authored credentials are explicit, never detected.**
  - `authentication := Profile with Credential` in `app%`.
  - Lower-level commands: `native_session_entity%` and
    `native_credential_storage% S for P using C session T`.
  - `Storage.profileEmail` was removed; it was unused.

### PostApp: the post's own `Credential`, `signUp` and `signIn`

`domain_post_app` serves the whole post `api` through `api := api`, including `getParty`'s
native join. It also routes `edit` (`Party.Changes`) and three extra plain operations
explicitly. **33/0**, with these checks:
- an unknown email and a wrong password give identical bytes and one KDF run each (54 ms vs
  49 ms)
- with the writer held by an external SQLite transaction, sign-up's KDF completes while
  the request is still waiting for admission
- sign-up is atomic (a session-table failure leaves no person or credential)
- sessions rotate
- `hostOnly` returns `hidden` with no names in the bytes
- composite-unique RSVP, notFound and ambiguous credentials

### Envelope (decisions 5 and 15)

Plain-body routes (`routes :=` and `api :=` apps) reply with `{"ok": v}`, `{"error": "ctor"}`
(domain, 422) and `{"error": "unauthorized"|"badRequest"|"notFound"|…}` at the class status.
Bare-integer refs and RFC 3339 times come from LeanReact's codecs. The precise framework code
goes in an `x-leanapp-error` header, and unknown routes return `{"error":"notFound"}` (404).
**Choice:** milestone 1 `operations :=` apps keep the Contract envelope (Partiful acceptance,
399), with the new ref and time encodings. `Nat` keeps its tagged form, which decision 15 does
not cover. `NativeApp.emitClient` passes `ClientRoute`s and the served manifest
(`manifestOverride`) for non-portable routes. The generated client is checked against both
apps: 9/9 each (templates, GET, plain bodies, both kinds of error).

### Generality

- **Library code.** No Partiful concept remains. A grep over `LeanApiDomain`, the README, the
  browser shell and the lakefile finds 4 hits, all false positives: the HTTP `host` and
  `Host` header ×3, and LeanReact's `CredentialLink.person` field ×1. The page shell now takes
  its title and navigation from the app.
- **Generality fixture** (`tests/LibraryApp.lean`, `scripts/ddd_library_acceptance.mjs`).
  Member/Book/Loan/MemberCredential, built from public API only:
  - a composite unique as the typed error `alreadyBorrowed`
  - `cascade% Loan.book`
  - the loan-history join
  - a librarian-only rule
  - `internal`, `Changes`
  - an `Option SignedIn` GET and `SignedIn` commands
  - authored join/sign-in with KDF hoisting
  - the new envelope
  - a migration: V1, then V2 refused without `addShelf`, then applied at startup
  - a curl transcript (`docs/ddd-m2-library-transcript.txt`)

  **26** checks, plus the generated client 9/9.

### Wave 3 gates (`leanapi-w3-gates.summary`, all exit 0)

| Gate | Result |
| --- | --- |
| App / common build | 322 / 499 jobs |
| `leanapi_tests` | 580/0 |
| `domain_route_checks` | 50/0 |
| `domain_post_app` | 33/0 |
| `ddd_check_domain.sh` | PASS (client 5/0) |
| `ddd_check_partiful.sh` | PASS (7 rejections; runs migration, library and post transcript) |
| Partiful acceptance | 399 |
| Curl acceptance | 24 |
| Migration acceptance | 35 |
| Post transcript | 6 (saved: `docs/ddd-m2-post-transcript.txt`) |
| Library acceptance | 26 |
| Generated client (post, library) | 9 / 9 |
| LeanJS audit | 13/0 |
| `git diff --check` | clean |

Protected file unchanged. Remaining gaps:
- There is no index on the credential's profile field, so verification scans the credential
  table.
- `Nat` keeps its tagged wire form.
- Token-mode replies are for non-browser clients; the generated client does not decode them.

## Wave 2 (2026-10-02): serving the portable layer

Built in place in `.lake/ddd-common` against `runs/partiful-m2/frozen-w2/leanreact` (LeanReact
wave 1) and, after LeanDB's checkpoint, `frozen-w2/LeanDB-cp1` (storage-step hooks). Scripts
and logs: `.lake/ddd-m2-scratch/leanapi-w2-*`. Milestone 1 surfaces, Partiful, routes, bearer
and the migration gate all still pass on these snapshots.

### 1. A portable `Api` is served

`app% X where authentication := a routes := [...] pages := [...] api := api` serves LeanReact's
`def api : Api := [post "/x" f, get "/y/:id" g]`. Each typed `api.f : Endpoint …` is
`Endpoint.post|get "/path" f.operation`; `app%` reads method, template and `f.operation` off it
(`LeanApi.Domain.apiEndpoints`) and runs the same `checkRoute`/`route_binding%` and
`assembleCommandAt`/`assembleQueryAt` path as explicit routes (which may also name
`f.operation` directly). An operation has one route (`PostApiDuplicate` fixture).

- Path binding from the portable template (`:party` binds `f.Input.party`).
- `ReadOp` → query → GET in a read snapshot; `Op` → command → one writer transaction.
- Requirements: `f.Requirements.infer` against `Native.resources s`.
- Actors through `Principal` (`LeanApiDomain/Principal.lean`):
  ```lean
  def Native.principalActor {A P} [Entity P] (principal : Principal A) (profile : principal.Profile = P) :
      ActorContext (fun _ => A) P                 -- SignedIn: live session (cookie or bearer), else 401
  def Native.optionalPrincipalActor … : ActorContext (fun _ => Option A) P   -- none only without a credential
  ```
  `f.Actor` is a plain definition and `Principal.Profile` a class projection; instance search
  unfolds neither, so `app%` passes `(Actor := fun _ => X)` and
  `(actorContext := principalActor (P := Profile) inferInstance rfl)`; `rfl` checks the
  profiles agree. The `assembleCommandAt`/`assembleQueryAt` instance binder is named `actorContext`.
- Manifest and allowlist follow the served route list. The generated client still refuses
  template/GET/plain-body routes until LeanReact checkpoint 1 (new client and envelope).
- Sessions: the post's `signUp`/`signIn` are not portable yet, so milestone 1's `auth%` runs
  over the post's `Person`. `native_auth_storage%` accepts the post's
  `constraint Person.uniqueEmail : unique email` (`Deriving.constraintDeclarations`) as the email key.

### 2. The new requests, through LeanDB's hooks (`Native.lean`, `NativeStorage.lean`)

| Request | Lowering |
| --- | --- |
| `insert` | `EntityStorage.insert value conflicts storageFault`: a declared unique conflict is a value |
| `update` | `EntityStorage.update row patch conflicts storageFault` |
| `delete` | `EntityStorage.delete row storageFault` (restricted → 409; cascades are the database's) |
| `findBy` | `EntityStorage.findBy lookup key` with `lookup : UniqueStorage storage key` |
| `select` | `EntityStorage.select` (by id) |
| `find` | unchanged |

`storageFault : LeanDb.Domain.StorageFault → CallError E` maps every fault to a framework reply
with `StorageFault.code` (invalidReference 400, invalidRow 422, missingReference/restricted/gone
409, invalidIdentity/unmappedConflict 500). `NativeResources` forwards
`HasUniqueResource (storageResources s) … → (Native.resources s) …`. My interim
implementations of these steps were removed in favor of the hooks.

### 3. The post-shaped app (`adapters/domain/tests/PostApp.lean`, `domain_post_app`)

Imports LeanReact's `tests.domain.PostPart1` unchanged, declares `cascade% Rsvp.party` (decision
8, until a portable `onDelete` exists) and serves the post's whole `api` with `api := api`, plus
a small portable `smallApi` (an `Option SignedIn` GET, `Party.update`, `Party.delete`,
`Party.select`) routed explicitly. **31 checks over SQLite**: exact manifest; decision 9
(token mode vs cookie mode); `emailTaken` from the `Person.uniqueEmail` value; `Clock.now` +
`require` (`dateInPast`, `alreadyStarted`); bearer `SignedIn`; 401 without a credential; a second
RSVP is the `onePerGuest` conflict value ("already going", one row); `getParty` through
`Viewer.of` → `Rsvp.findBy`: `everyone` shows names, `hostOnly` gives an attendee `hidden` with no
name in the bytes and the host the list, invalid bearer 401, `notFound`; `notHost`; update,
select; cancelling a party deletes its RSVPs and keeps people; GET on a command route is 405.

Still the milestone 1 wire encodings (`Ref` objects, tagged `int`/`nat`, Contract envelope);
decisions 5/15 switch with LeanReact checkpoint 1. The guest join (`LinkStorage.project`) waits
for LeanReact's `RequestF.linkField`; today `Party.guests` runs as the portable select loop.

### Wave 2 gate results (`.lake/ddd-m2-scratch/leanapi-w2-gates.summary`, LeanDB-cp1)

| Gate | Result |
| --- | --- |
| App build (Partiful) | PASS, 318 jobs |
| Common build | PASS, 492 jobs |
| `leanapi_tests` | **580/0** |
| `domain_route_checks` | **50/0** |
| `domain_post_app` (new) | **31/0** |
| `ddd_check_domain.sh` | PASS (client 5/0, 5 rejections, 3 audits) |
| `ddd_check_partiful.sh` | PASS (route, migration 35, post app 31, prepared 11/0, KDF, **7** rejections incl. `PostApiDuplicate`, 5 audits) |
| Partiful acceptance | **399** |
| Curl acceptance | **22** |
| Migration acceptance | **35** |
| LeanJS audit | **13/0** |
| `git diff --check` | clean |

Disk stayed between about 0.7 and 1.0 GB free; no ENOSPC.

### Waiting on

- **LeanReact checkpoint 1:** portable auth types and KDF metadata (authored `signUp`/`signIn`
  with design D hoisting), the decision 5/15 envelope and wire values, the client for
  templates/GET/plain bodies, and `RequestF.linkField` for the guest join.

## Wave 1.5 (2026-10-02): decision 9 and the migration gate

Built against the **live** `/Users/harshwork/code/LeanDB` (now stable) and the frozen
leanreact.

**Decision 9.** An anonymous command (no session cookie, no bearer) skips the Origin
check only in token mode (`Accept: application/vnd.leanapp.token`); no cookie is set then.

*Apps with no accounts (2026-10-04).* `app% Name where api := api` has no credential and no
session table, so it has no ambient credential: no cookie it set, no session it could resolve.
Origin and CSRF exist to stop a cross-site page from using a visitor's credential, or from
planting one, which is decision 9's case. Without accounts there is nothing to use or plant,
and a cross-site POST can do exactly what `curl -X POST` can. So its commands need no Origin or
CSRF check. Presented credentials (cookies, `Authorization`) are ignored rather than refused
with 401. They can name nobody, and a browser sends a host's cookies to every port of that
host, so a 401 would break requests that carry another local app's cookies. Apps with
accounts are unchanged.
This now holds for every anonymous command (`ActorContext (fun _ => Unit)` passes
`Auth.tokenRequested req` to `Auth.anonymousGuard`), not just sign-up/sign-in. Cookie-mode
sign-up and sign-in with no Origin or a wrong Origin are still 403 and set no cookie.
Tests: `domain_route_checks` (token sign-in and sign-up without Origin; cookie-mode
sign-up with no/wrong Origin; cookie-mode sign-in with wrong Origin) and
`scripts/ddd_route_acceptance.mjs`, which now opens with the post's transcript over real
curl and writes it to `RUN/transcript.txt`: token sign-up, host with bearer, second
sign-up, RSVP with bearer, duplicate email → `emailTaken` (422), RSVP with no credential
→ `unauthenticated` (401). Replies are still Contract envelopes (decision 5 pending).

**Migration gate at startup** (LeanDB `Gate.ensure` / `Gate.command?`):

```lean
structure NativeApp … where …
  migrations : List LeanDb.SchemaMigration := []
def NativeApp.gate (app) (config : AppConfig) : IO (Option UInt32)     -- refusal → exit code
def NativeApp.main (app) (args : List String) (config : AppConfig := {}) : IO UInt32
def NativeApp.serve (app) (config : AppConfig := {}) : IO Unit         -- = main [], exits on refusal
```

- `NativeApp.main`: `LEANAPP_EMIT_CLIENT`, then `LEANAPP_*` overrides, then
  `Gate.command?` (`migrate --check` read-only, exit 0/3/1; `migrate` applies), then
  `Gate.ensure`: a covered change is applied and reported (`status: migrated …`); an
  uncovered one prints the gate's message (every `Entity.field`) to stderr, serves
  nothing and exits 3. Unknown arguments exit 2. `serve` runs the same gate.
- `app% … pages := [...] migrations := [ addGuestList := Party.addField guestList (fill := .everyone) ]`.
  An entry `name := term` is declared by `app%` through LeanDB's `migration%` after it has
  derived the native schema (a `migration%` written before `app%` cannot see the native
  `Entity` instance `app%` creates); it is named `<App>.name` and recorded by LeanDB under
  `name`. A bare `name` refers to an existing `LeanDb.SchemaMigration`.
- `partiful migrate [--check]`: a `main : IO Unit` cannot see process arguments, so the
  staged launcher (`PartifulLaunch`, the `partiful` executable) is the authored Main with
  its one `main` line adapted to `def main (args : List String) : IO UInt32 :=
  Partiful.app.main args { … }`; `partiful_server` stays byte-for-byte. DDD-PF-01 should
  make that one-line change in `partiful/Main.lean`. `lake exe partiful migrate --check`
  in the staged workspace prints `status: fresh …` and creates no file.
- Test with a real old database (`adapters/domain/tests/MigrationChecks.lean`, run by
  `scripts/ddd_migration_acceptance.mjs`, 35 checks): V1 serves and stores a person, a
  session and parties; the V2 build (Party gains a required `guestList`) without its
  migration refuses `migrate --check` / `migrate` / startup with exit 3 naming
  `Party.guestList`, leaving rows, columns and LeanDB metadata unchanged; with the
  migration, `migrate --check` is `pending` (read-only), startup applies it and serves,
  existing parties read `everyone`, every old value is kept, a session issued under V1
  still works, the id counter carries over, `_leandb_applied_migrations` records
  `addGuestList`; afterwards `up to date`, `migrate` is idempotent, a restart applies
  nothing, and the V1 build refuses the newer database (field removed).

Wave 1.5 gate results (logs `.lake/ddd-m2w15-*.log`, script in the session scratchpad):

| Gate | Result |
| --- | --- |
| App build (`ddd_partiful.py` with live LeanDB) | PASS, 306 jobs |
| Common build | PASS, 475 jobs |
| `leanapi_tests` | **580/0** |
| `domain_route_checks` | **50/0** |
| `ddd_check_domain.sh` | PASS (client 5/0, 5 rejections, 3 audits) |
| `ddd_check_partiful.sh` | PASS (route 50/0, migration acceptance 35, prepared 11/0, KDF gate, 6 rejections, 5 audits) |
| Partiful acceptance | **399 checks** (adds `partiful migrate --check` / `migrate` / bad argument) |
| Curl acceptance | **22 checks** (post transcript + decision 9) |
| Migration acceptance | **35 checks** |
| `git diff --check` | clean |

Note: at 00:32 another agent's run executed this session's old wave 1 gate script (both
were named `gates.sh` in the shared scratchpad) against the frozen LeanDB. All gates were
then re-run from `.lake/ddd-m2-scratch/leanapi-gates.sh` (summary
`.lake/ddd-m2-scratch/leanapi-gates.summary`, logs `leanapi-*.log` next to it), with the
same results as the table above plus LeanJS audit 13/0. The rebuild was in place: deleting
under `.lake` is blocked here, and the disk had about 0.5 GB free, too little for a second
workspace. Lake rechecked every content-hash trace against the live-LeanDB lakefile; all
475 common jobs replayed, so the outputs already matched live LeanDB. The stale
`.lake/ddd-m2-gates.summary` and `.lake/ddd-m2-final-*.log` now hold a one-line STALE
marker; they were overwritten, not deleted.

## What landed

### A. Bearer transport alongside cookies (decision 1)

`adapters/domain/LeanApiDomain/Auth.lean`, `Native.lean`, `Runtime.lean`, `Contract.lean`.

- A request presents at most one session credential:
  `Auth.presented config req : Except (CallError Empty) Presented` with
  `inductive Presented | none | cookie (token) | bearer (token)`.
  `Authorization: Bearer <token>` is parsed by `Auth.bearerToken`; another scheme, a
  repeated header or a malformed token is a refused credential (401). The session cookie
  together with any `Authorization` header is `auth.ambiguous_credentials`, a 400 protocol
  error (`{"tag":"protocol","code":"auth.ambiguous_credentials"}`, the Contract envelope's
  badRequest).
- `Auth.resolve` resolves both transports through the same `store.live` lookup: one session
  table, SHA-256 digest, exact expiry, revocation, credential version, enabled flag and live
  profile. Only the cookie, an ambient credential, gets the Origin and CSRF checks on a
  mutation. Bearer requests need neither.
- Anonymous commands: `Auth.anonymousGuard config req (tokenReply)` keeps the exact
  Origin check, except for a request presenting a bearer token, or (decision 9) a token-mode
  request carrying no session cookie. Anonymous reads (Unit actor, `mutation = false`) no
  longer require Origin (see Interface changes).
- Sign-up and sign-in: `Auth.tokenRequested req` is true when `Accept` lists
  `application/vnd.leanapp.token` (`Auth.tokenMediaType`). Then the success value is
  `{"profile": <ref>, "token": <raw 43-char token>}` (`Prepared.tokenEdits`, through the new
  `ReplyEdits.value` hook), with no `Set-Cookie`, no CSRF cookie and no
  `x-leanapp-auth-csrf`. Otherwise behavior is unchanged: HttpOnly session cookie, readable
  CSRF cookie and marker, profile ref in the body, token never in a body. KDF preparation
  still runs before writer admission under `KDFGate` in both modes. A presented live
  session, cookie or bearer, is revoked in the same transaction (rotation).
- New `ActorContext` instance for the post's `Option SignedIn` actor:
  `fun scope => Option (SignedIn scope Profile)`; `none` only when no credential is presented.

### B. Explicit route list (native half of DDD-LAPI-05)

`adapters/domain/LeanApiDomain/Routes.lean` (new), `Contract.lean`, `Execution.lean`,
`Runtime.lean`, `App.lean`.

- A publication now carries a `RouteBinding`: method (GET/POST), path template
  (`/parties/:party/rsvp`), the typed path fields, the body format, and a body limit.
  `:name` binds the input field `name`; the remaining fields come from the body.
  `BodyFormat.plain` is the post's request shape (the input record without path fields;
  empty body = `{}`; GET takes no body). `BodyFormat.envelope` is the milestone 1 Contract
  request envelope (generated client). A body that also supplies a path field is
  `request.path_field_in_body` (400); an undecodable segment is a typed decode error (400).
- `route_binding% post "/parties/:party/rsvp" Op` is the checked binding term. At
  elaboration (`checkRoute`): every `:name` must name a field of the operation's input
  record, that field's type must have `PathParam` and `Wire` instances, and `get` accepts
  only a query operation whose inputs all come from the path. Each failure names the
  parameter (or field) and the operation, e.g.
  `path parameter :id in "/parties/:id/rsvp" has no matching input field in RouteChecks.rsvp; its input fields are party`
  and `GET "/parties/:party/rsvp" requires a query operation, but RouteChecks.rsvp is a command; publish it with post`.
- `PathParam` instances: `Ref T`, `Nat`, `Int`, `String`, `Name`, `Title`, `Instant`.
  `Password`, `Email` and `Text` deliberately have none.
- `app%` gains a routes form. Only the listed entries are routable, in the manifest and in
  the client allowlist; an operation has one route:

  ```lean
  app% RouteChecks.app where
    authentication := RouteChecks.account
    routes := [
      post "/sign-up" RouteChecks.account.signUp,
      post "/sign-in" RouteChecks.account.signIn,
      post "/parties" RouteChecks.host,
      get  "/parties/:party" RouteChecks.partyTitle,
      post "/parties/:party/rsvp" RouteChecks.rsvp
    ]
    pages := [ "/parties/:party" => RouteChecks.signInPage ]
  ```

  The milestone 1 form `operations := [...]` is unchanged in behavior: it is now sugar for
  `rpcBinding op` entries (`POST /api/<ns>/<name>`, envelope) through the same generic path.
  The served Partiful manifest is byte-identical to the generated client's `manifest.json`.
- `Application.create` validates every binding again at runtime (template syntax, path
  fields equal template parameters, path fields exist in the input schema, GET only for a
  read effect and path-only input, method/template conflicts including `/api/manifest`).
  `Application.manifestJson` keeps exact milestone 1 bytes for portable bindings and adds
  `{path, method, maxBodyBytes, params, body}` for templates, GET and plain bodies.
- A page and a GET endpoint may share a path (the post's `/parties/:party`): a request whose
  `Accept` lists `text/html` gets the page, any other client (curl, `fetch` default `*/*`)
  gets the endpoint.
- The generated browser client (frozen LeanContract) speaks literal POST envelopes only, so
  `NativeApp.emitClient` and `Application.emitClient` refuse an app with template, GET or
  plain-body routes instead of emitting a client that disagrees with the served manifest.
  This lifts in wave 2 (see Interface for peers).

### C. DDD-LAPI-07, LeanAPI side

- `AppConfig.port` defaults to 8080, and `AppConfig.host` to `127.0.0.1`. `LEANAPP_PORT`,
  `LEANAPP_HOST` (`0.0.0.0` in a container), `LEANAPP_DATABASE`, `LEANAPP_BROWSER_DIR`,
  `LEANAPP_CLOCK_FILE` and `LEANAPP_EMIT_CLIENT` still override.
- The executable finds its bundle without `LEANAPP_BROWSER_DIR`:
  `NativeApp.browserCandidates` tries an explicit directory, then
  `<exe>/../../../../.lake/ddd-browser/<App>` (the build workspace of `.lake/build/bin/<exe>`),
  then the working directory. Apps without pages need no bundle.
- Lake target, implemented and exercised in the staged workspace (`scripts/ddd_partiful.py`
  writes it): `partiful_server` (the authored Main as is), `target partiful_browser`
  (runs `partiful_server` with `LEANAPP_EMIT_CLIENT`, stages App.mjs and the LeanReact
  runtime, runs esbuild with `NODE_PATH`; rebuilt when the server binary or any staged
  source changes, replayed otherwise), and `lean_exe partiful` whose root
  `PartifulLaunch` (`import PartifulMain`) `needs := #[partiful_browser]`. The launcher
  breaks the cycle a direct `needs` on `PartifulMain` would create. Result:
  `cd .lake/ddd-common && lake exe partiful` with no `LEANAPP_*` variable built the bundle,
  started on the authored port 3000, and served `/api/manifest`, `/sign-up`,
  `/assets/app.mjs` (1.99 MB) and a token sign-up. The acceptance now runs the binary
  without `LEANAPP_BROWSER_DIR` from an unrelated working directory.
- `NativeApp.withService app config k` factors database/auth/service assembly out of
  `serve`, so tests drive the exact service in process.

### D. Design note: hoisting `password.hash` and `Credential.verify` (decision 4)

Goal: the post writes `← password.hash` and `← Credential.verify person password` inside an
`Op`; no KDF may run while holding the writer, KDF work stays bounded by `KDFGate`, and an
unknown email does the same work as a wrong password.

1. IR. Replace the coarse `RequestF.signUp`/`signIn` nodes by three requests:
   `hashPassword (password : Password) : … PasswordHash`,
   `verifyCredential (storage) (person : Option (Row Scope T)) (password : Password) : … (Option (Ref T))`,
   `startSession (storage) (person : Ref T) : … Session`. `Password.hash`,
   `Credential.verify` and `Auth.startSession` are their smart constructors in `Op`.
2. Metadata. Contract derivation records the KDF steps an operation can reach, keyed by
   the input field they consume: `kdf : List KdfStep`, `KdfStep := .hash (field) | .verify (field)`
   (the same kind of record LR-05 item 8 keeps for effects and touched fields).
3. Preparation (before admission, outside the writer, inside `KDFGate.run`):
   - `.hash f`: scrypt the decoded input field `f` once; memo `password ↦ hash`. Done even
     if the flow will later fail (e.g. `emailTaken`), which is the milestone 1 cost profile.
   - `.verify f`: run the flow's read prefix on a read snapshot with a preparation algebra
     (`Flow.run` over `ExceptT Stop (Read s)`: reads answered, the first write request or
     domain failure stops). At `verifyCredential row? p`, read the candidate credential for
     `row?` (none, missing or disabled uses the existing dummy hash), verify, and memo
     `(row?.id, p) ↦ (result, credential version, hash)`.
   - Session token and CSRF material are generated here too (cheap, outside the writer).
4. Admission. The writer runs the whole flow with the command algebra. `hashPassword p` is
   answered from the memo by constant-time password equality; a password that is not a
   prepared input field fails closed (`auth.preparation_required`, as today).
   `verifyCredential row? p` is answered from the memo only if `row?.id` is the prepared
   candidate and the live credential's version and hash equal the prepared ones; otherwise
   it returns `none`, the post's `wrongEmailOrPassword` path, which is the milestone 1
   stale-preparation rule. `startSession` inserts the session row with the prepared digests,
   revokes a presented session and returns the transport-specific reply edits (cookie or
   token) applied only after commit.
5. Tests to port: the injected external writer lock shows scrypt completes before writer
   acquisition; unknown email and wrong password give identical bytes and dummy work;
   stale version/hash between preparation and admission is refused; `KDFGate` capacity and
   release. The existing tests cover these for the derived flow.

Portable hooks needed from LeanReact: the three request constructors and smart
constructors (item 1), the `kdf` metadata (item 2), and a `PasswordHash`/`Session` type with
no `Wire`/`Repr` for `PasswordHash` and the two `Session` wire shapes (below). Nothing else:
the preparation pass is an ordinary `Algebra` over the existing `Flow.run`.

## Commands and results

All builds use `LEAN_NUM_THREADS=2` and the installed Lean 4.33.0. `F=…/runs/partiful-m2/frozen`,
`NM=/Users/harshwork/code/leanreact/node_modules` (read only; the frozen copy has none).

| Gate | Command | Result |
| --- | --- | --- |
| Common build | `python3 scripts/ddd_prepare_common.py $F/LeanDB $F/leanreact --sqlite …/LeanDB/.lake/packages/leansqlite`; `lake build leanapi_tests domain_contract_checks domain_prepared_checks domain_native_read_checks domain_native_command_checks domain_kdf_gate_checks domain_route_checks` | PASS, 468 jobs |
| Core tests | `.lake/ddd-common/.lake/build/bin/leanapi_tests` | **580 passed, 0 failed** (core is unchanged) |
| Route/bearer checks (new) | `.lake/ddd-common/.lake/build/bin/domain_route_checks` | **45 passed, 0 failed** |
| Domain checks | `bash scripts/ddd_check_domain.sh .lake/ddd-common $F/leanreact` | PASS: auth fixture, contract fixture, client 5/0, 5 compiler rejections, 3 kernel audits |
| Partiful checks | `bash scripts/ddd_check_partiful.sh .lake/ddd-common` | PASS: route checks, native command/read, prepared 11/0, KDF gate, **6** compiler rejections (2 existing + 4 new route fixtures), 5 kernel audits |
| App build | `python3 scripts/ddd_partiful.py $F/LeanDB $F/leanreact <spec> --sqlite … --node-modules $NM` | PASS, 302 jobs, bundle built by the Lake target |
| `lake exe` | `cd .lake/ddd-common && lake exe partiful` (no `LEANAPP_*`) | serves manifest, pages, bundle, token sign-up |
| Acceptance | `node scripts/ddd_partiful_acceptance.mjs .lake/ddd-common $F/leanreact $NM` | **396 checks PASS** (341 at milestone 1 plus bearer), no `LEANAPP_BROWSER_DIR` |
| Route acceptance (new) | `node scripts/ddd_route_acceptance.mjs .lake/ddd-common` | **16 checks PASS**, real `curl` over a socket and SQLite |
| LeanJS audit | `python3 scripts/ddd_audit_leanjs.py $F/leanreact .lake/ddd-common/.lake/build/lib/lean .lake/ddd-m2-js --lean <4.33>/bin/lean --node-modules $NM` | **13/0** |
| Whitespace | `git diff --check` (tracked files) and a trailing-whitespace scan of the untracked owned files | clean |

Bearer coverage over real HTTP and SQLite (acceptance and route acceptance): curl-style
sign-up with a token request, then RSVP and host with bearer and no CSRF or Origin; missing,
unknown, malformed and other-scheme credentials give 401 (and an invalid bearer never
becomes anonymous); rotation and a revoked session row are refused; the exact expiry
cutoff is honored for reads and mutations; a cookie request without CSRF (or Origin) still
fails while the same request with them succeeds; cookie plus bearer is 400; a default
sign-in body never contains the token or the word "token", and a default sign-in still
needs Origin; a failed token sign-in returns no token. Route coverage: exact manifest of
listed routes with methods/templates/params; unlisted and old name-derived paths are 404;
path binding for POST and GET; invalid segment and body-supplied path field are 400; GET
on a POST route is 405; GET with a body is 400; page/endpoint negotiation on one path;
runtime refusal of a GET binding for a command and of an unbound parameter; four
compile-time negative fixtures.

Logs: `.lake/ddd-m2-*.log`, receipts under `.lake/ddd-acceptance/` and
`.lake/ddd-route-acceptance/`.

## Interface for peers

### Native signatures (namespace `LeanApi.Domain`)

```lean
inductive BodyFormat | envelope | plain
structure PathField where
  name : String
  decode : String → Ontology.Validation Lean.Json
structure RouteBinding where
  method : LeanApi.Method := .post          -- .get or .post
  path : String                             -- "/parties/:party/rsvp"
  fields : List PathField := []             -- exactly the template's :params, in order
  format : BodyFormat := .plain
  maxBodyBytes : Option Nat := some 16384
def RouteBinding.rpc (http : LeanApp.HttpBinding) : RouteBinding
def RouteBinding.validate (b : RouteBinding) (writes : Bool) (input : Ontology.WireSchema) : Ontology.Validation Unit
def RouteBinding.portable? (b : RouteBinding) : Option LeanApp.HttpBinding
def RouteBinding.toJson (b : RouteBinding) : Lean.Json
def parseRouteTemplate (path : String) : Except String (List TemplateSegment)

class PathParam (T : Type) where parse : String → Ontology.Validation T
def PathField.of (name : String) (T : Type) [PathParam T] [Ontology.Wire T] : PathField
def checkRoute (method template : String) (operation : Lean.Name) : MetaM (Array RouteField)
syntax "route_binding% " ident str ident : term          -- route_binding% post "/x/:a" Op

def rpcBinding (op : LeanApp.Domain.Operation k Actor I O E) : RouteBinding
def assembleCommandAt (context : Context s Profile) (codecs : Contract.Http.Codecs) (binding : RouteBinding)
    (op : LeanApp.Domain.Operation .command Actor I O E) (requirements : op.Requirements (Native.resources s)) : Published s
def assembleQueryAt   (context) (codecs) (binding) (op : LeanApp.Domain.Operation .query Actor I O E) (requirements) : Published s
def publishSignUpAt (context) (codecs) (binding) (account : Account Profile) (requirements) : Published s
def publishSignInAt (context) (codecs) (binding) (account : Account Profile) (requirements) : Published s
-- unchanged signatures, now rpcBinding sugar: assembleCommand, assembleQuery, publishSignUp, publishSignIn
TrustedAdapter.queryAt / commandAt / preparedCommandAt  -- RouteBinding in place of HttpBinding
Application.create (ps : List (Published s)) : Validation (Application s)   -- validates bindings
Application.manifestJson : Application s → Lean.Json
Application.bindings : Application s → List RouteBinding

Auth.presented (config) (req) : Except (CallError Empty) Auth.Presented
Auth.bearerToken (req) : Except (CallError Empty) (Option String)
Auth.tokenRequested (req) : Bool;  Auth.tokenMediaType := "application/vnd.leanapp.token"
Auth.anonymousGuard (config) (req) (tokenReply := false) : Except (CallError Empty) Unit
Auth.Prepared.tokenEdits (prepared) : ReplyEdits
ReplyEdits.value : Option (Lean.Json → Lean.Json)
instance : Native.ActorContext (fun scope => Option (SignedIn scope Profile)) Profile

AppConfig.port := 8080
NativeApp.descriptions : List (LeanApp.PublicOperation × Contract.Http.ErrorStatus × RouteBinding)
describeAt (binding) (op) / describe (op)
NativeApp.withService (app) (config) (k : Context s Profile → Service → IO α) : IO α
NativeApp.browserCandidates / findBrowser / configure
```

Wire facts: token reply value `{"profile": <ref>, "token": <string>}`; ambiguous
credentials `{"tag":"protocol","code":"auth.ambiguous_credentials"}` 400; responses are
still the Contract envelopes until the portable decision 5 envelope exists.

### What wave 2 needs from LeanReact

1. `Endpoint` exposing: method (`get`/`post`), the path template string, the operation in
   today's shape (`LeanApp.Domain.Operation kind Actor Input Output Error`, i.e. contract,
   `Requirements`, `bodyWithResources`) or an equivalent, plus a way to obtain
   `op.Requirements (Native.resources s)` generically (today `op.Requirements.infer`).
   LeanAPI then does `assembleCommandAt context codecs (RouteBinding.ofEndpoint e) e.op req`.
2. Path fields: either the endpoint's list `(argName, segment → Validation Json)` or the
   argument types so LeanAPI's `PathParam` resolves them. Preferably move `PathParam` into
   the portable layer (the browser needs the same segment codec to build URLs) and LeanAPI
   reuses it. Path parameter ↔ argument name checks then live in the `post`/`get`
   elaborators; LeanAPI keeps its runtime `validate`.
3. Kind index: `ReadOp` contracts carry `OperationKind.query`, so `get` keeps its native
   check (`http.get_requires_query`).
4. Decision 5 envelope as portable functions: success, domain error (constructor name, or
   `{tag, …fields}`), and framework error with its status. LeanAPI swaps `resultReply`,
   `frameworkReply` and `successResponse` to them in one place (`Contract.lean`).
5. Generated client: path template substitution, GET, plain request bodies, and the new
   envelope; or consume LeanAPI's manifest `http` form `{path, method, maxBodyBytes, params, body}`.
   Until then the native layer refuses to emit a client for such routes.
6. Auth vocabulary (DDD-LAPI-06): `Session` wire shapes (profile ref for cookie clients,
   `{profile, token}` for token requests), the IR requests and `kdf` metadata of design D,
   and `SignedIn`/`Option SignedIn` actor families mapping to the native `SignedIn` and
   `Option SignedIn` dictionaries.

### What the app repository's lakefile will need (DDD-LAPI-07 with DDD-LAPI-04)

`domain_driven_development` must move from `lakefile.toml` to `lakefile.lean` (custom
targets need Lean). Once DDD-LAPI-04 pins one graph (authorized revisions of LeanAPI with
`adapters/domain`, LeanReact, LeanDB with `adapters/domain`, leansqlite, leancrypto, all on
Lean 4.33.0), it needs:

```lean
import Lake
open System Lake DSL

package partiful where
  moreLinkArgs := #[<OpenSSL libcrypto.a>]   -- until leancrypto links it (as ddd_prepare_common.py does)

require «leanapi-domain» from git "<leanapi url>" @ "<pinned rev>" / "adapters/domain"
require leanreact from git "<leanreact url>" @ "<pinned rev>"
require leandb from git "<LeanDB url>" @ "<pinned rev>"     -- must expose LeanDb and LeanDbDomain

lean_lib Partiful where                      -- Domain, Views (module paths must match directory case)
lean_lib PartifulApp where roots := #[`Main] -- Main: app% … and main, as authored

lean_exe partiful_server where root := `Main

target partiful_browser pkg : FilePath := do
  let some server ← findLeanExe? `partiful_server | error "partiful_server is not declared"
  let some api ← findPackageByName? `«leanapi-domain» | error "leanapi-domain missing"
  let some react ← findPackageByName? `leanreact | error "leanreact missing"
  -- entry := api.dir / "browser" / "App.mjs"; engine := react.dir / "engine";
  -- esbuild := react.dir / "node_modules" / ".bin" / "esbuild"
  -- then exactly the body of partiful_browser in scripts/ddd_partiful.py
  -- (emit with LEANAPP_EMIT_CLIENT, stage runtime, esbuild with NODE_PATH)

lean_exe partiful where
  root := `Launch                             -- Launch.lean: `import Main`, nothing else
  needs := #[partiful_browser]
```

Prerequisites outside Lake: Node and LeanReact's `node_modules` (esbuild) installed once
(`npm ci` in the LeanReact package, a download this run did not perform), and the OpenSSL
static library. `partiful/Main.lean` should drop `port := 3000` (or use 8080) to match the
post, and its `app%` should move to the `routes :=` form when the post's paths land
(wave 2). Python is then needed only for the development stager.

## Interface changes

- `AppConfig.port` default 3000 → 8080 (decision 6). Partiful's Main passes 3000 explicitly,
  so it still listens on 3000 until DDD-PF-01 edits it.
- `NativeApp.descriptions` and `describe` carry the `RouteBinding` (triple instead of pair).
  `Published` has a `route` field; `ReplyEdits` has `value`. Constructors stay private.
- `app%` keywords `authentication`, `operations`, `routes`, `pages` are now non-reserved
  (`&"…"`): adding `routes` as a reserved token would have broken `x.routes` in importing
  files, and the old ones blocked those identifiers too.
- Anonymous (Unit actor) reads no longer require Origin; anonymous commands still do unless
  they present a bearer token or are in token mode with no cookie (decision 9). Needed for
  `get` routes and the post's transcript from curl.
- Naming deviation: the native checked binding is spelled `route_binding% post "…" op`;
  the post's `post`/`get` belong to LeanReact's portable `Endpoint` (wave 2). Inside `app%`
  the entries read `post "…" op` / `get "…" op`.
- `scripts/ddd_partiful.py` gains `--sqlite` and `--node-modules`; the acceptance takes an
  optional third argument (node_modules); the audit takes `--node-modules`. Defaults are
  unchanged.

## Decisions recorded

- Path parameter decode failures are typed 400 decode errors, not 404.
- One route per operation (`app%` rejects a second entry; `Application.create` rejects a
  duplicate identity).
- A body supplying a path-bound field is refused, never merged.
- GET routes take every input from the path (no query string yet); GET with a body is 400.
- Token requests return the token in the success value and set no cookie, so they need no
  Origin; rotation still revokes whatever session the request presented.
- New native tests live in `domain_route_checks`, not `leanapi_tests`, so core keeps no
  dependency on the adapter, LeanReact or LeanJS.
- `Accept: text/html` selects the page when a page and a GET endpoint share a path.

## Remaining gaps

- Response envelope is still the Contract envelope (decision 5 needs the portable
  definition); request bodies are plain only on explicit routes.
- No generated browser client for template/GET/plain routes (refused, by design, until
  wave 2); Partiful stays on `operations :=` with RPC paths.
- Authored `signUp`/`signIn` and KDF hoisting are designed (D), not implemented: they need
  LeanReact's IR and metadata. `auth%` remains the implementation.
- Per decision 9, credential-less anonymous commands outside token mode still need Origin,
  so the post's pre-auth `curl -X POST /people` needs token mode (or an Origin header).
- `app%` must be used with a fully qualified name at top level (as Partiful's Main does);
  inside a `namespace` its generated `native_schema%` name is not rooted. Pre-existing.
- Not a fresh-clone release: the app repository's lakefile and pinned graph (DDD-LAPI-04)
  are documented above, not built. Core axiom audit was not re-run (core unchanged).
- `partiful migrate` needs the authored Main to take arguments (see wave 1.5); the
  staged launcher adapts that one line. The LeanJS audit was not re-run in wave 1.5
  (leanreact frozen and unchanged; no LeanJS input changed).

## Next step

Wave 2: switch the build to live LeanReact once it ships `Endpoint`/`Op`/`ReadOp` and the
decision 5 envelope; add `RouteBinding.ofEndpoint`, swap the reply encoders, implement
design D on the new IR requests, then port Partiful's `app%` to `routes :=` with the post's
paths and re-run every gate above.

## Changed owned files (this wave)

`adapters/domain/LeanApiDomain/{Auth,Contract,Execution,Native,Runtime,App}.lean`,
new `adapters/domain/LeanApiDomain/Routes.lean`, new `adapters/domain/tests/RouteChecks.lean`,
new `adapters/domain/tests/negative/{RouteMissingParam,RouteGetCommand,RouteAppEntry,RoutePathCodec}.lean`,
`adapters/domain/README.md`, `scripts/{ddd_prepare_common.py,ddd_partiful.py,ddd_partiful_acceptance.mjs,ddd_check_partiful.sh,ddd_audit_leanjs.py}`,
new `scripts/ddd_route_acceptance.mjs`, and this file. Wave 1.5 adds
`adapters/domain/tests/MigrationChecks.lean` and `scripts/ddd_migration_acceptance.mjs`,
and edits `App.lean`, `Native.lean`, `RouteChecks.lean`, `ddd_partiful.py`,
`ddd_prepare_common.py`, `ddd_check_partiful.sh`, `ddd_partiful_acceptance.mjs` and
`ddd_route_acceptance.mjs`. No peer files were written; no
commits. Generated outputs are under the owned, ignored `.lake/`.
