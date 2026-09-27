/-
  The goals of LeanAPI, as Lean statements.

  What LeanAPI is for is written in intent.md and DESIGN.md §1. Here each
  goal is a `Prop` wherever one can be written today, with where it stands:

  * `proved`: the kernel checked a proof of exactly this statement;
  * `open`: stated, not proved; the ticket is the work that proves it;
  * `unstated`: the words to state it do not exist yet; the ticket is the
    work that brings them.

  A goal moves from unstated to open to proved, and this file cannot claim
  more than the proofs give. `#goals` lists the goals; the list at the end
  of this file is checked on every build, and a proved goal whose proof
  uses `sorry`, `native_decide` or an axiom beyond `propext`,
  `Classical.choice` and `Quot.sound` fails it.

  **Not goals here:**
  * feature parity with Express and FastAPI (intent.md) is a list, not a
    statement: README.md lists it and `examples/starter/smoke.sh` runs it;
  * guarantees about which code compiles: that only authentication makes an
    `Auth`, that a `GET` handler cannot write, that `api!` refuses
    conflicting routes. They are not statements about values; the
    `#guard_msgs` tests in `tests/Tests/Endpoint.lean` pin them.

  **Trusted, under every proved goal:** Lean's kernel. Proofs are about the
  Lean meaning of the code; that the running server does what the meaning
  says also trusts Lean's compiler, `Std.Http` and SQLite
  (`executionIsMeaning` below). The architecture goals are about the import
  graph `imports%` reads, and trust that elaborator.
-/
import Architecture.Framework
import Architecture.Apps

namespace Architecture.Goals

open Lean LeanApi LeanApi.Props

/-- A LeanAPI ticket, `tickets/LAPI-nn-….md`. -/
structure Ticket where
  number : Nat
  deriving Repr

open Elab Term in
/-- `ticket% 6` is ticket LAPI-06; it fails if `tickets/` has no such file. -/
elab "ticket% " n:num : term => do
  let k := n.getNat
  let pre := s!"LAPI-{if k < 10 then "0" else ""}{k}-"
  let files ← System.FilePath.readDir "tickets"
  unless files.any (·.fileName.startsWith pre) do
    throwErrorAt n "ticket%: no file tickets/{pre}….md"
  return mkApp (mkConst ``Ticket.mk) (mkRawNatLit k)

/-- Where a stated goal stands. -/
inductive Standing (P : Prop) : Type where
  /-- The kernel checked `proof`. -/
  | proved (proof : P)
  /-- Stated, not proved yet. -/
  | open (next : Ticket)

/-- A goal: its statement and where it stands, or the ticket that brings
    the words to state it. -/
inductive Goal : Type where
  | stated (statement : Prop) (standing : Standing statement)
  | unstated (needs : Ticket)

/-! ## 1. An API server: handlers see only valid input, and reads do not write -/

/-- **GET and HEAD never change the state**, for every typed API. -/
def safeMethodsChangeNothing : Goal := .stated
  (∀ {σ : Type} (api : Api σ) (env : Env) (r : Req) (s : σ),
    r.method.Safe → (api.step env r s).2 = s)
  (.proved fun api env r s h => Api.step_safe api env r s h)

/-- **Input that does not decode never reaches the handler**, nor does a
    request that does not authenticate: the answer is the same whatever the
    handler is, and the state does not change. For path parameters; for
    query parameters, headers, cookies and bodies; and for `Auth`. -/
def badInputNeverReachesTheHandler : Goal := .stated
  ((∀ {σ α β : Type} [FromParam α] [Handler σ β] (f g : Path α → β) env r (s : σ) i,
      (∀ a, pathAt (α := α) r i ≠ .ok a) →
      Handler.step f env r s i = Handler.step g env r s i ∧ (Handler.step f env r s i).2 = s) ∧
   (∀ {σ α β : Type} [R : FromRequest σ α] [Handler σ β] (f g : α → β) env r (s : σ) i,
      (∀ a, R.extract s env r ≠ .ok a) →
      Handler.step f env r s i = Handler.step g env r s i ∧ (Handler.step f env r s i).2 = s) ∧
   (∀ {σ α β : Type} [A : Authenticates σ α] [ViewOf σ α] [Handler σ β] (f g : Auth α → β)
      env r (s : σ) i,
      (∀ a, A.authenticate s env r ≠ .ok a) →
      Handler.step f env r s i = Handler.step g env r s i ∧ (Handler.step f env r s i).2 = s))
  (.proved ⟨fun f g _ _ _ i h => Handler.path_failed f g i h,
            fun f g _ _ _ i h => Handler.input_failed f g i h,
            fun f g _ _ _ i h => Handler.auth_failed f g i h⟩)

/-! ## 2. Properties you state and prove: invariants, isolation, idempotence (intent.md) -/

/-- **An invariant holds in every reachable state** if it holds initially
    and every endpoint preserves it. What preserving asks of an endpoint is
    computed from its signature: nothing for a read. -/
def invariantsFromSignatures : Goal := .stated
  (∀ {σ : Type} (api : Api σ) (init I : σ → Prop),
    (∀ s, init s → I s) → (∀ e ∈ api, e.Preserved I) →
    ∀ s, (api.toSys init).Reachable s → I s)
  (.proved fun api _ _ hinit hp => Invariant.of_inductive (Api.inductive_of api hinit hp))

/-- **A response depends only on what the caller may see.** For a request
    that authenticates as `p`, two states that look the same to `p` give
    the same response, if each endpoint meets its isolation obligation,
    which is computed from its signature. Covers the routes of `api`. -/
def isolationFromSignatures : Goal := .stated
  (∀ {σ α : Type} [A : Authenticates σ α] [V : ViewOf σ α] (api : Api σ) (p : α),
    (∀ e ∈ api, e.Isolated fun env r s₁ s₂ => V.same p s₁ s₂ ∧ A.authenticate s₁ env r = .ok p) →
    ∀ env r (s₁ s₂ : σ), V.same p s₁ s₂ → A.authenticate s₁ env r = .ok p →
    (api.step env r s₁).1 = (api.step env r s₂).1)
  (.proved fun api p hiso env r _ _ hv ha => Api.noninterference api p hiso env r hv ha)

/-- **A retried request is applied once.** In any system wrapped by
    `Keyed`, a keyed request replayed after any sequence of other requests
    gets the recorded response, marked as a replay, and changes nothing;
    reusing the key for a different request is refused and changes
    nothing. -/
def retriesApplyOnce : Goal := .stated
  ((∀ (S : Sys) {Scope Fp : Type} [DecidableEq Fp] (scope : S.Req → Scope) (fp : S.Req → Fp)
      (led : Ledger (Scope × String) (Fp × S.Res)), LedgerLaws led →
      ∀ (r : S.Req) (key : String) (e e' : S.Env) (w : (Keyed S scope fp led).World),
      led.lookup w.2 (scope r, key) = none →
      ∀ between, let wn := Keyed.run _ between ((Keyed S scope fp led).step e (r, some key) w).2
        (Keyed S scope fp led).step e' (r, some key) wn = (.replay (S.step e r w.1).1, wn)) ∧
   (∀ (S : Sys) {Scope Fp : Type} [DecidableEq Fp] (scope : S.Req → Scope) (fp : S.Req → Fp)
      (led : Ledger (Scope × String) (Fp × S.Res))
      (r : S.Req) (key : String) (e : S.Env) (w : (Keyed S scope fp led).World) (f : Fp) (res : S.Res),
      led.lookup w.2 (scope r, key) = some (f, res) → f ≠ fp r →
      (Keyed S scope fp led).step e (r, some key) w = (.keyReused, w)))
  (.proved ⟨by
      intro _ _ _ _ _ _ _ hl r key e e' w h between
      exact Keyed.keyed_replay_after hl r key e e' w h between,
    by
      intro _ _ _ _ _ _ _ r key e w f res h hf
      exact Keyed.keyed_reuse r key e w f res h hf⟩)

/-! ## 3. Domain meaning carried into LeanDB (intent.md) -/

/-- **Every row a program reads satisfies its table's invariant.** It holds
    by construction: reads return `Valid` rows, which carry the proof. -/
def rowsSatisfyInvariants : Goal := .stated
  (∀ (α : Type) [LeanDb.Entity α] (row : LeanDb.Valid α), LeanDb.Invariant α row.val)
  (.proved fun _ _ row => row.property)

/-- **A database endpoint's program means what the API says.** For every
    endpoint, the program the server runs denotes the endpoint's step: its
    response and the next state. -/
def programsMeanTheirSteps : Goal := .stated
  (∀ {s : Type} [LeanDb.IsSchema s] (api : DbApi s), ∀ e ∈ api, ∀ env r st,
    (e.prog env r).denote st = e.step env r st)
  (.proved fun api => DbApi.prog_denote api)

/-- **The running server does what the meaning says**: SQLite executes each
    program as `denote` says, so every theorem above holds of the server.
    Today this is trusted. It needs LeanDB's execution law (M15). -/
def executionIsMeaning : Goal := .unstated (ticket% 6)

/-! ## 4. Row-level security, from the API to the database (DESIGN §1, §7.5)

These need LeanDB's views (M16): the database as `me` sees it, `S.As me`. -/

/-- **Restricted reads**: a program over `S.As p` observes only the rows
    `p`'s policies admit; two states that agree on them give the same
    result. -/
def restrictedReads : Goal := .unstated (ticket% 14)

/-- **Write confinement**: a transaction over `S.As p` leaves unchanged every
    row `p`'s policies do not admit. -/
def writeConfinement : Goal := .unstated (ticket% 14)

/-- **Isolation for every route, with no obligation per endpoint**: an API
    whose authenticated programs are all over `S.As me` is noninterfering. -/
def isolationForEveryRoute : Goal := .unstated (ticket% 14)

/-- **Reachable is proved**: the server serves only an API whose programs
    are over views, unless marked trusted, so the routes a client can reach
    are the routes the theorems cover. -/
def reachableIsProved : Goal := .unstated (ticket% 14)

/-! ## 5. The shape: rules do not depend on transport (DESIGN §3.2) -/

/-- **The proofs are about plain code.** The property library, typed
    endpoints and database endpoints never reach the server or `Std.Http`,
    through any chain of LeanAPI's imports. -/
def proofsAreAboutPlainCode : Goal := .stated
  (Framework.NeverReaches .props .server ∧ Framework.NeverReaches .props .transport ∧
   Framework.NeverReaches .endpoints .server ∧ Framework.NeverReaches .endpoints .transport ∧
   Framework.NeverReaches .database .server ∧ Framework.NeverReaches .database .transport)
  (.proved ⟨Framework.props_never_reach_the_server.1, Framework.props_never_reach_the_server.2.1,
            Framework.endpoints_never_reach_the_transport.1, Framework.endpoints_never_reach_the_transport.2,
            Framework.database_never_reaches_the_transport.1, Framework.database_never_reaches_the_transport.2⟩)

/-- **Business rules do not depend on HTTP.** In the example applications,
    the domain reaches neither HTTP nor LeanDB, and the schema and policies
    reach the actor (`Auth`) but never the rest of LeanAPI. -/
def rulesIgnoreHttp : Goal := .stated
  (Apps.NeverReaches .domain .http ∧ Apps.NeverReaches .domain .leandb ∧
   Apps.NeverReaches .schema .http ∧ Apps.NeverReaches .policies .http ∧
   Apps.NeverReaches .policyLib .http)
  (.proved ⟨Apps.domain_is_plain_lean.1, Apps.domain_is_plain_lean.2.1,
            Apps.rules_never_reach_http.1, Apps.rules_never_reach_http.2.1,
            Apps.rules_never_reach_http.2.2⟩)

/-- **One module speaks `Std.Http`**: `LeanApi.Runtime.Server`, so a change
    in the transport between toolchains stays in one file. -/
def oneDoorToTheTransport : Goal := .stated
  (∀ e ∈ Framework.imports.edges, e.2 = `Std.Http → e.1 = `LeanApi.Runtime.Server)
  (.proved Framework.only_the_server_imports_std_http)

/-! ## The list -/

open Elab Command Meta in
/-- List this namespace's goals in the order they are declared, with where
    each stands. Fails if a proved goal's proof uses an axiom beyond
    `propext`, `Classical.choice` and `Quot.sound`. -/
elab "#goals" : command => do
  let env ← getEnv
  let ns := `Architecture.Goals
  let mut goals : Array (Nat × Name) := #[]
  for (n, ci) in env.constants.map₂.toList do
    if ns.isPrefixOf n && ci.type.isConstOf ``Goal then
      let line := (← findDeclarationRanges? n).map (·.range.pos.line) |>.getD 0
      goals := goals.push (line, n)
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut rows : Array String := #[]
  for (_, n) in goals.qsort (·.1 < ·.1) do
    let some v := (env.find? n).bind (·.value?) | continue
    let short := n.componentsRev.head!.toString
    let (standing, next) := match v.getAppFnArgs with
      | (``Goal.stated, #[_, st]) => match st.getAppFnArgs with
        | (``Standing.proved, _) => ("proved", none)
        | (``Standing.open, #[_, t]) => ("open", t.appArg!.rawNatLit?)
        | _ => ("?", none)
      | (``Goal.unstated, #[t]) => ("unstated", t.appArg!.rawNatLit?)
      | _ => ("?", none)
    if standing == "proved" then
      let bad := (← liftCoreM (collectAxioms n)).filter (!allowed.contains ·)
      unless bad.isEmpty do
        throwError "#goals: `{short}` is marked proved, but its proof uses {bad.toList}"
    let ticket := match next with
      | some k => s!" (LAPI-{if k < 10 then "0" else ""}{k})"
      | none => ""
    rows := rows.push s!"{standing}{ticket}: {short}"
  logInfo m!"{"\n".intercalate rows.toList}"

/--
info: proved: safeMethodsChangeNothing
proved: badInputNeverReachesTheHandler
proved: invariantsFromSignatures
proved: isolationFromSignatures
proved: retriesApplyOnce
proved: rowsSatisfyInvariants
proved: programsMeanTheirSteps
unstated (LAPI-06): executionIsMeaning
unstated (LAPI-14): restrictedReads
unstated (LAPI-14): writeConfinement
unstated (LAPI-14): isolationForEveryRoute
unstated (LAPI-14): reachableIsProved
proved: proofsAreAboutPlainCode
proved: rulesIgnoreHttp
proved: oneDoorToTheTransport
-/
#guard_msgs in
#goals

end Architecture.Goals
