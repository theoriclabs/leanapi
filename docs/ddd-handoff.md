# LeanAPI Partiful handoff

Updated 2026-09-30. The actual small authored Partiful app builds and runs locally:
**eight operations, four page URLs, one native server, SQLite, compiled derived
browser**. No app-owned handlers/DTOs/rows/schema/parsers/policy SQL were added.
All changes remain uncommitted. The user review file is untouched.

## Build and run the authored app

From the LeanAPI root, with the existing source checkouts and installed dependencies:

```sh
LEAN_NUM_THREADS=2 python3 scripts/ddd_partiful.py "$LEANDB_REPO" "$LEANREACT_REPO" "$DDD_SPEC_REPO"
LEANAPP_DATABASE=partiful.db LEANAPP_PORT=3000 \
LEANAPP_BROWSER_DIR="$PWD/.lake/ddd-common/.lake/ddd-browser/Partiful.app" \
.lake/ddd-common/.lake/build/bin/partiful
node scripts/ddd_partiful_acceptance.mjs .lake/ddd-common "$LEANREACT_REPO"
```

Open `http://127.0.0.1:3000/sign-up`. Remaining URLs are `/sign-in`,
`/parties/new`, `/parties/{id}`. Origin is the exact configured loopback address;
use that address for browser mutations. No deployment/publication is involved.

The build stages original Domain/Views/Main into owned ignored output and emits
LeanJS ESM, the exact Contract client/manifest, page metadata and a bundled browser
entry. Current root Main imports `LeanApiDomain.App`, so all three staged sources
are byte-for-byte authored files. The older import alias remains accepted by the
stager. No per-Partiful source rewrite or replacement flow body occurs.
`--prepare-only` emits the local graph without building. `LEANAPP_EMIT_CLIENT`
selects generated-client inspection without opening DB/auth/server.

`app%` produces:

```lean
Partiful.app : LeanApi.Domain.NativeApp Partiful.app.Database Partiful.Person
LeanApi.Domain.NativeApp.serve app (config : AppConfig := {}) : IO Unit
```

`AppConfig` has database, port, explicit origin, development, browserDirectory and
clockFile. Existing `.serve {database := "partiful.db", port := 3000}` is unchanged.
Development CLI overrides: `LEANAPP_DATABASE`, `LEANAPP_PORT`, `LEANAPP_BROWSER_DIR`,
`LEANAPP_CLOCK_FILE`. Clock file contains epoch seconds, sampled inside the actual
admitted transaction/snapshot, never on queue entry. Production cookie configuration
requires an explicit HTTPS origin and `development := false`.

## Generic native execution and exact storage evidence

Import `LeanApiDomain.App`; lower-level modules are individually importable under
`adapters/domain/LeanApiDomain`. Namespace is `LeanApi.Domain`, separate from core
module names. Core LeanAPI has no browser/compiler dependency.

`Native.resources S` reuses `LeanDb.Domain.storageResources S` entity/member/
projection slots and replaces only auth with `fun storage => Auth.Storage S _ storage`.
No second portable vocabulary or IR exists. `Native.readRequest`, `commandRequest`,
`queryAlgebra`, `commandAlgebra`, `contains`, and `project` are total over current
shared IR constructors. Runtime publishers execute **shared `Flow.run`** on each
operation's generated `Requirements (Native.resources S)` and `bodyWithResources`.

- Find uses carried coherent EntityStorage and original checked records/ref codecs.
- Create maps the actual typed native unique alternative through
  `EntityStorage.sourceUnique` to its generated semantic closed error. FK identities
  are handled separately. Unknown constraints are redacted typed framework failures;
  they never become an unrelated `emailTaken`.
- Change rereads the live original row in the transaction and patches only the
  generated changed native fields. The native `TouchingUnique`/`TouchingFK` variants
  map separately. Gone/invalid failures retain their own framework channels.
- Remove uses actual generated ReferencedBy capabilities and typed restriction
  identity; member parent deletion cascades through DB-owned relation storage.
- Include consumes the authenticated actor ID and actual MemberStorage. The DB-owned
  exact pair uniqueness is the only idempotent duplicate. No host exception exists.
- Policy membership uses the restricted algebra hook; no public Request.contains.
- Guarded ProjectionF.members consumes the carried DB ProjectionStorage/FieldStorage,
  with actual target dictionary, fieldTy/value equality and getter/path agreement.
  `selection.project relation.parent` selects **only guest names**, never Person/email
  rows. Shared Flow.run evaluates policy before preparing this SQL. map uses the
  authored pure projection function. Hidden is canonical payload-free unit.

`ActorContext` is a native capability for SignedIn/Viewer/Unit, resolving live actor,
viewer, time and mutation CSRF in the same operation transaction/read snapshot.
Invalid supplied cookies fail; anonymous Viewer exists only when cookie is absent.
`assembleCommand` and `assembleQuery` need only operation + generated requirements.
No native request name dispatch or per-Partiful HTTP body exists.

`executePrepared` consumes **DB-owned** `Txn.runPrepared`/`Read.runPrepared`; API has
no outer transaction around these runners. `prepared_abort_restores` consumes
`Txn.denote_abort_restores`. Write domain/framework errors abort before cookies.
Existing core `DbProg.execWithEnv` preserves its old-pin runner compatibility.
Clock/Env injection reaches existing DbEndpoint routes through `toRouteWithEnv`.

## Generated authentication, KDF preparation and cookies

Portable `auth%` supplies the two operation contracts, shared parsers/closed errors
and typed Account accessors: signUpProfile/signUpPassword/signInEmail/signInPassword.
`native_auth_entities% account` generates private Credential and Session entities;
`native_auth_storage% S for account` generates coherent Auth.Storage and a concrete
HasAuthResource for the **exact canonical profile EntityStorage**. The concrete
provider resolves a dependent dictionary inference limitation without a cast or
alternate store. Neither private entity has Wire or enters the publication manifest.

`Auth.Storage S Profile profile` carries actual profile/credential/session storage,
lookup/make/accessor/revoke capabilities. `Auth.Admission` is sealed Type-0 native
preparation, has no public codec or authority. Existing scrypt, dummy verification,
secure opaque Tokens and SHA digest/cookie helpers are reused. There is no new auth
engine. KDFGate uses Std.Mutex to bound concurrent expensive preparation independently
of the writer, and releases slots on success or an observable exception.

The signin candidate snapshot prepares credentials without sampling a decision
clock. Final operation time is sampled only after actual writer BEGIN admission.
Signup hashes outside writer admission, then creates canonical profile, credential
and session atomically inside it. Signin verifies outside the writer, then rereads
canonical live profile, credential enabled/version/hash and checks the preparation
inside the admitted transaction. Session issuance and revocation of a presented live
session are atomic. A failed rotation rolls back. Cookies are returned only after
commit. The same committed ReplyEdits includes x-leanapp-auth-csrf containing only
the already-readable CSRF value. Browser per-call response capture compares this
marker to the current readable cookie before accepting the typed public actor:
older auth bodies cannot overwrite a newer committed session. No session bearer
or new JSON field/operation is added. Pending success has a bounded completion
turn so an unmounted form cannot indefinitely suppress scope invalidation. Password bytes are preserved; only email uses the one shared canonical parser.

Raw session tokens exist only in HttpOnly Set-Cookie. Public auth output is a nominal
profile ref. Persisted credentials/sessions contain hash/digests, never plaintext or
raw bearer. Production cookies: __Host-leanapp_session (HttpOnly) and readable
__Host-leanapp_csrf; Secure/Path=/, no Domain, SameSite=Strict. Explicit loopback HTTP
uses leanapp_session/leanapp_csrf. Stored CSRF digest is checked against exactly one
mutation header and exact configured Origin. No Host/Forwarded header trust.

The generic browser shell reads CSRF on every mutation, including after reload;
never reads/copies session tokens to JS/localStorage. Auth changes rotate scoped
actor/generation and clear protected mounted resources. Shell requestClient factory
for forms/screens delivers actual AbortSignal via shared ResourceRequest cleanup.
Unauthenticated framework callbacks clear authority once, avoiding repeated401
remount loops. Late authorized responses cannot repopulate a newer actor scope.

Page GET restores only public actorRef and CSRF cookie NAME from the same live
snapshot. Invalid supplied credentials return401. There is no ninth whoami operation.
Exactly two auth + host/rsvp/edit/reschedule/cancel/partyPage are published. Exact
allowlist is used for native routes, /api/manifest and generated client. HTTP cookies
never enter its JSON manifest. Replies/errors/body limits are private,no-store,
typed/redacted Contract envelopes; native exception-text logging is disabled.

## Current validation

All builds use LEAN_NUM_THREADS=2; direct Lean uses -j2 (Lake5 has no -j option).
Ignored logs/receipts are under owned `.lake`. Tests are actual nonempty execution,
not a substitute service. Current commands/results:

- `python3 scripts/ddd_partiful.py <DB> <LR> <spec>`: PASS, 296 jobs, original root
  native Main plus LeanJS/browser bundle. Source staging is byte-for-byte.
- `node scripts/ddd_partiful_acceptance.mjs .lake/ddd-common <LR>`: **341 checks PASS**,
  latest receipt `.lake/ddd-acceptance/353cc1e1b3b1bf92/receipt.json`;
  `.lake/ddd-partiful-acceptance.log`. Actual HTTP/SQLite/Chromium signup→host→second
  signup→RSVP→visibility→reschedule→restart→cancel. Exact8 manifest/no ninth;
  full nonempty anonymous/host/nonmember/member public/attendees/private matrix;
  private hides even attending host; retry/exact cutoff/host guards; canonical and
  concurrent signup collisions; complete late-session rollback/counters; invalid
  drafts/actor injection/scope refs/cookies/Origin/CSRF; unknown/wrong signin/password
  bytes; revoke/version/hash recheck, disabled/deleted profile/exact expiry; injected
  external writer lock proves acquisition precedes clock; names-only SQL despite
  corrupt unselected email; hidden bytes independent of membership/count; browser
  CSRF after reload, server restart/persistence, native401 clears protected resource
  with bounded request count, real delayed nonempty authorized response+policy/auth
  change cannot reappear and actual scoped fetch aborts; browser canonical collision
  field feedback/raw draft, invalid-password no-transport retention and compiled
  signin/session rotation; two actual distinct profile auth responses complete out
  of order, and the older body cannot replace the newest cookie actor/generation.
  Failed commands carry no committed auth marker. Corruption/drop phases are
  deliberate fault fixtures excluded from WF claims.
- Current `lake build leanapi_tests domain_contract_checks domain_prepared_checks
  domain_native_read_checks domain_native_command_checks`: PASS, 404 jobs.
- Current common `.lake/build/bin/leanapi_tests`: **580 passed/0 failed**,
  `.lake/ddd-common-final-tests.log`.
- `domain_native_command_checks`: PASS populated two-unique create/change alternatives,
  touched-field closed errors, actual late generated Flow abort, every table/counter
  and WF preservation, unmapped typed FK framework channel;
  `.lake/ddd-native-command-final-tests.log`.
- `bash scripts/ddd_check_domain.sh .lake/ddd-common <LR>`: PASS native scrypt,
  client→actual HTTP framing→SQLite envelopes; generated JS client **5/0**, five
  intended compiler rejections (actor Wire/private construction/scope/raw
  publication/query write), three standard kernel audits. Log
  `.lake/ddd-common-domain-final.log`.
- `bash scripts/ddd_check_partiful.sh .lake/ddd-common`: PASS native command/read,
  prepared actual HTTP fixture + **11 clock/0**, synchronized KDF capacity/exception release,
  two precise compiler negatives
  (unchanged email unique is absent from name-change Error; generated private
  Credential/Session lack Wire), five standard kernel audits including actual
  Partiful.app and native create/change/project. Log `.lake/ddd-partiful-focused.log`.
- `python3 scripts/ddd_audit_leanjs.py <LR> .lake/ddd-common/.lake/build/lib/lean
  .lake/ddd-js-4.33 --lean <installed4.33/bin/lean>`: **13/0** JS parity/compiler,
  deterministic generation, module/hooks/proof fields and intended compiler
  negatives. Log `.lake/ddd-js-4.33.log`.
- Current common core axiom audit: **332 theorems PASS**, only
  propext/Classical.choice/Quot.sound. Log `.lake/ddd-common-axiom-audit.log`.

## Compatibility, guarantees and remaining release work

Supported unified local graph is installed **Lean4.33.0/current API/DB/LR sources**.
The existing root nightly core baseline remains unchanged; previously580/0 passed
there as well. Nightly browser is unsupported: Decidable ABI changed to Bool/proof
record and generated countdown failed. 4.33 LeanJS corpus parity is the selected
baseline. Std.Http blocking socket behavior is not a performance qualification.

No toolchain or dependency checkout was downloaded. Existing SQLite static archive,
OpenSSL, crypto checkout, peer node_modules/Chromium are reused. The local graph is
explicitly generated/ignored from CLI paths; no developer-local paths occur in
release manifests. Checkout HEADs (plus uncommitted work): API6415f7c0d52c3944f13d2cfd455cc3981f291661,
DB27876b5f506f35dc033c92cbef90f6b9f90d4421,
LRc975968bfc7b46fbb2104b8996cfc4b7429755d3. Those HEADs alone do not contain this
implementation. **This is not a pinned published/fresh-clone release**; release pins
must follow review and authorized peer commits. No commits/push/publication allowed.
The separate optional package still defaults to the released Contract-only target.

Runtime/SQLite/FFI/crypto and trusted actor construction are explicit trust boundaries.
Shared Flow query/DB rollback and generated column/key proofs use standard Lean
foundations; no sorry/axiom/unsafe type/proof cast was introduced. The whole stack
is not claimed formally verified. Unrestricted Ontology Ref inhabitants still need
checked DB conversion; no universal LawfulEntity/Ref codec law is fabricated.
General imported-namespace resource closure, unrestricted logical invariant/WF
correspondence and general semantic FK closure remain explicit shared limitations;
unsupported storage constraints fail closed as framework errors. App closure covers
current auth profile namespace plus generated private auth and DB-owned relations.
Calendar editor years1..9999 UTC; wire epochs remain signed64 exact. Low-level trusted
native storage APIs remain privileged. Ticket-wide formal/release/evolution claims
are broader than this completed local runtime milestone.

All final focused gates passed and git diff --check is clean. Next step: review the
uncommitted owned diff and receipts;
when peer implementations have authorized revisions, pin the optional release graph
and repeat fresh-clone qualification. The actual local app assembly is implemented.


## Changed owned files

This follow-up adds/updates `adapters/domain/LeanApiDomain/{NativeStorage,
NativeResources,Native,NativeRead,Auth,AuthStorage,AuthDeriving,Runtime,App}.lean`,
`adapters/domain/browser/App.mjs`, `adapters/domain/README.md`,
`adapters/domain/tests/{NativeReadChecks,NativeCommandsChecks,KDFGateChecks}.lean`,
`adapters/domain/tests/negative/{UnchangedUnique,AuthStoreWire}.lean`,
`scripts/{ddd_prepare_common.py,ddd_partiful.py,ddd_partiful_acceptance.mjs,
ddd_check_partiful.sh}` and this handoff.

Retained earlier foundations in the owned uncommitted diff: core
`LeanApi/Http/{DbEndpoint,DbProblem,Endpoint}.lean`,
`LeanApi/Runtime/{Blocking,Server}.lean`, new `LeanApi/Storage/Bounds.lean`;
compatibility proof changes in Billing/Helpdesk/Scheduling Schema,
PrivateGames/Storage/Schema and PrivateGames/DbApi; tests/Main,
Tests/{DbEndpoint,TransactionClock}; scripts/audited_theorems.txt;
optional adapter package/aggregate, Contract/Execution/Identity/Prepared;
AuthChecks/ContractFixture/ContractChecks/PreparedChecks, client.test.mjs,
five authority/effect compiler negatives; scripts/{ddd_prepare_native,
ddd_compile_portable,ddd_audit_leanjs}.py and ddd_check_domain.sh.

No staged files, commits, remote messages or peer source changes were made.
User `Review_harsh_2026-09-23.md` remains untouched. Generated/ignored files were
not deleted. No .codex/.agents/.aws configuration was altered.
