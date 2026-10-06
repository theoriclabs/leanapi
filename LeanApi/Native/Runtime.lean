import LeanApi.Native.Native

namespace LeanApi.Native
open LeanApi LeanDb LeanDb.Model LeanApi.Core

/-- Bounded KDF admission is independent of the database writer. -/
structure KDFGate where
  active : Std.Mutex Nat
  limit : Nat := 2
  /-- Completed KDF runs, when observed (tests compare the work of two requests). -/
  runs : Option (Std.Mutex Nat) := none

def KDFGate.run (gate : KDFGate) (work : IO A) : IO (Contract.CallResult A E) := do
  let admitted ← gate.active.atomically do
    let count ← get
    if count < gate.limit then
      set (count + 1)
      pure true
    else pure false
  if !admitted then return .error (Native.fault "auth.busy" 503)
  try
    let result ← work
    if let some runs := gate.runs then runs.atomically (modify (· + 1))
    return .ok result
  finally gate.active.atomically (modify (· - 1))

structure Context (s Profile : Type) [IsSchema s] [LeanDb.Model.Entity Profile] : Type 1 where
  profile : LeanDb.Native.EntityStorage s Profile
  store : Auth.Storage s Profile profile
  dc : DbConns
  cookies : Auth.CookieConfig
  fresh : IO Env := Env.fresh
  ttl : Nat := 86400
  dummyHash : String
  kdf : KDFGate

private def resolveRead {s Profile Actor Scope E} [IsSchema s] [LeanDb.Model.Entity Profile]
    [Native.ActorContext Actor Profile] (context : Context s Profile) (env : Env) (req : Req)
    (mutation : Bool) : Read s (Contract.CallResult (Actor Scope) E) :=
  Native.ActorContext.resolve context.store context.cookies env req mutation

private def resolveCommand {s Profile Actor Scope E} [IsSchema s] [LeanDb.Model.Entity Profile]
    [Native.ActorContext Actor Profile] (context : Context s Profile) (env : Env) (req : Req) :
    Native.CommandM Scope s E (Actor Scope) :=
  (Txn.ofRead (resolveRead context env req true)).orAbort id

/-! ## Authored authentication: KDF hoisting (design D)

An operation whose metadata lists KDF steps (`FlowMetadata.kdf`) or starts a session is
prepared before writer admission. `.hash f` scrypts input field `f`; `.verify f` runs the
flow's read prefix in a snapshot up to its `verifyCredential` (the probe) to learn the profile
and the stored hash, then verifies there, the dummy hash standing in for a missing profile
(decision 2). All KDF work runs under `KDFGate`, never inside the writer. The admitted flow's
requests are answered from the preparation and rechecked against the live credential. -/

/-- Where the read prefix stopped: at a `verifyCredential` (profile key and stored hash), or
before reaching one. -/
inductive Probe where
  | stop
  | verify (profile : Option String) (stored : Option String)

/-- A read step of the prefix, in the snapshot; a write stops the probe. -/
private def probeStorage {s A} [IsSchema s] :
    StorageRequest (LeanDb.Native.storageResources s) Unit .command A → ExceptT Probe (Read s) A
  | @StorageRequest.find _ _ _ _ inst storage reference =>
    letI := inst
    match storage.find reference with
    | .ok program => liftM program
    | .error _ => throw .stop
  | @StorageRequest.findBy _ _ _ _ _ inst storage _ lookup key => do
    letI := inst
    match ← liftM (storage.findBy lookup key) with
    | .ok row => pure row
    | .error _ => throw .stop
  | @StorageRequest.select _ _ _ _ inst storage => do
    letI := inst
    match ← liftM storage.select with
    | .ok rows => pure rows
    | .error _ => throw .stop
  | @StorageRequest.linkField _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent =>
    match link.project targets column parent with
    | .error _ => throw .stop
    | .ok program => liftM program
  | _ => throw .stop

private def probeRequest {s A} [IsSchema s] (env : Env) :
    LeanApi.Core.Request Unit .command A (Native.resources s) → ExceptT Probe (Read s) A
  | .now => match Instant.ofEpochSeconds (Int.ofNat env.now) with
    | .ok now => pure now
    | .error _ => throw .stop
  | .storage req => probeStorage req
  | @RequestF.verifyCredential _ _ _ _ _ instanceC credentials link subject _ => do
    letI := instanceC
    match subject with
    | none => throw (.verify none none)
    | some row => do
      match ← liftM (Native.storedHash (E := Empty) credentials link row.id) with
      | .ok stored => throw (.verify (some row.id.key) stored)
      | .error _ => throw .stop
  | _ => throw .stop

private def probeAlgebra {s} [IsSchema s] (env : Env) :
    Algebra (ExceptT Probe (Read s)) .command Unit (Native.resources s) :=
  ⟨probeRequest env⟩

private def passwordField (fields : Lean.Json) (field : String) : Option Password :=
  match fields.getObjVal? field with
  | .ok (.str raw) => (Ontology.Password.parse raw).toOption
  | _ => none

/-- Preparation before writer admission. Refused requests (Origin, credentials) do no KDF. -/
def prepareAuthored {s Profile Actor I O E} [IsSchema s] [LeanDb.Model.Entity Profile]
    [actorContext : Native.ActorContext Actor Profile] (context : Context s Profile)
    (operation : LeanApi.Core.Operation .command Actor I O E)
    (requirements : operation.Requirements (Native.resources s)) (req : Req) (input : I) :
    IO (Contract.CallResult Auth.Preparation E) := do
  if let .error error := Auth.anonymousGuard context.cookies req (Auth.tokenRequested req) then
    return .error (error.mapDomain Empty.elim)
  let fields := operation.contract.inputCodec.encode input
  let mut hashes : List (Password × String) := []
  let mut verifications : List Auth.Verified := []
  for step in operation.metadata.kdf do
    match step with
    | .hash field =>
      let some password := passwordField fields field | return .error (Native.fault "auth.kdf_input_missing")
      match ← context.kdf.run (E := E) (hashPassword password.value) with
      | .error error => return .error error
      | .ok hash => hashes := hashes ++ [(password, hash)]
    | .verify field =>
      let some password := passwordField fields field | return .error (Native.fault "auth.kdf_input_missing")
      let probe : Env → Read s (Contract.CallResult Probe E) := fun env => do
        match ← Native.ActorContext.resolve (Actor := Actor) (Scope := Unit) context.store context.cookies env req false with
        | .error error => return .error error
        | .ok actor =>
          match ← (Flow.run (probeAlgebra env) (operation.bodyWithResources requirements actor input)).run with
          | .error probe => return .ok probe
          | .ok _ => return .ok .stop
      let found ← match ← context.dc.read (Read.runPrepared (do context.fresh) probe) with
        | .error .busy => return .error (Native.fault "storage.busy" 503)
        | .error .stopped | .ok (.error _) => return .error (Native.fault "storage.unavailable")
        | .ok (.ok (.error fault)) => return .error (Native.fault (if fault matches .corruption _ then "storage.corrupt" else "storage.unavailable") (faultStatus fault))
        | .ok (.ok (.ok (.error error))) => return .error error
        | .ok (.ok (.ok (.ok probe))) => pure probe
      let (profile, stored) := match found with
        | .verify profile stored => (profile, stored)
        | .stop => (none, none)
      match ← context.kdf.run (E := E) (Auth.verifyPrepared profile password stored context.dummyHash) with
      | .error error => return .error error
      | .ok verified => verifications := verifications ++ [verified]
  return .ok (Auth.Preparation.create hashes verifications (← Auth.prepareSession ""))

/-- A plain operation that hashes, verifies or starts a session: prepared before admission;
in the transaction, a presented session is rotated, the flow runs against the preparation,
and the session it started is delivered after commit (cookie, or token-mode body). -/
def assembleAuthoredAt {s Profile Actor I O E} [IsSchema s] [LeanDb.Model.Entity Profile]
    [actorContext : Native.ActorContext Actor Profile] (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (binding : RouteBinding) (operation : LeanApi.Core.Operation .command Actor I O E)
    (requirements : operation.Requirements (Native.resources s)) : Published s :=
  TrustedAdapter.preparedCommandAt codecs operation.contract
    (prepareAuthored context operation requirements)
    (fun env req input preparation => do
      let actor ← resolveCommand (Actor := Actor) context env req
      if operation.metadata.establishesSession then
        match Auth.presented context.cookies req with
        | .error error => Txn.throw (error.mapDomain Empty.elim)
        | .ok credential =>
          if let some token := credential.token? then context.store.revoke (Tokens.digest token)
      match ← Flow.run (Native.commandAlgebra env context.ttl (some preparation))
          (operation.bodyWithResources requirements actor input) with
      | .error error => Txn.throw (.domain error)
      | .ok output =>
        let started ← Txn.ofRead (context.store.started preparation.session)
        let edits : ReplyEdits := if !started then {}
          else if Auth.tokenRequested req then preparation.session.tokenEdits
          else preparation.session.replyEdits context.cookies context.ttl
        return (output, edits))
    (fun _ => 422) binding

/-- Publish a generated command at an explicit route (see `route_binding%`). Operations that
reach KDF steps or start a session take the prepared path. -/
def assembleCommandAt {s Profile Actor I O E} [IsSchema s] [LeanDb.Model.Entity Profile]
    [actorContext : Native.ActorContext Actor Profile] (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (binding : RouteBinding) (operation : LeanApi.Core.Operation .command Actor I O E)
    (requirements : operation.Requirements (Native.resources s)) : Published s :=
  if operation.metadata.kdf.isEmpty && !operation.metadata.establishesSession then
    publishCommandWithResourcesAt codecs operation requirements (resolveCommand (Actor := Actor) context)
      (fun env => Native.commandAlgebra env) (fun _ => 422) binding
  else assembleAuthoredAt context codecs binding operation requirements

/-- Publish a generated query at an explicit route; GET is allowed only here. -/
def assembleQueryAt {s Profile Actor I O E} [IsSchema s] [LeanDb.Model.Entity Profile]
    [actorContext : Native.ActorContext Actor Profile] (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (binding : RouteBinding) (operation : LeanApi.Core.Operation .query Actor I O E)
    (requirements : operation.Requirements (Native.resources s)) : Published s :=
  publishQueryCheckedWithResourcesAt codecs operation requirements
    (fun env req => resolveRead (Actor := Actor) context env req false) Native.queryAlgebra
    (fun _ => 422) binding

/-! ## Apps with no accounts

An app with no accounts (`app% Name where api := api`) has no credential, no session table
and no actor: each of its operations takes none (`Unit`). Two rules follow, recorded next to
decision 9:

* **Presented credentials are ignored, not refused.** The app issues none, so a cookie or an
  `Authorization` header can name nobody and authorize nothing. A browser also sends a host's
  cookies to every port of that host, so refusing them would break requests that carry
  another local app's cookies.
* **Commands need no Origin or CSRF check.** Those checks stop a cross-site page from using a
  visitor's ambient credential, or from planting one (decision 9). Without accounts there is
  none, so a cross-site request can do only what any client can, such as `curl -X POST`. -/

/-- An operation of an app with no accounts must not hash, verify or start a session: there is
no credential or session table to answer it. Refused when the app is assembled. -/
def requireNoAccounts (operation : LeanApi.Core.Operation k Actor I O E) : Ontology.Validation Unit :=
  if operation.metadata.kdf.isEmpty && !operation.metadata.establishesSession then .ok ()
  else .error (Ontology.ValidationErrors.single "app.accounts_required"
    (params := [("operation", operation.contract.identity.namespaceName ++ "." ++ operation.contract.identity.name)]))

/-- Publish a command of an app with no accounts at an explicit route: no actor to resolve, no
Origin or CSRF check, presented credentials ignored. -/
def assemblePublicCommandAt {s I O E} [IsSchema s] (codecs : Contract.Http.Codecs) (binding : RouteBinding)
    (operation : LeanApi.Core.Operation .command (fun _ => Unit) I O E)
    (requirements : operation.Requirements (Native.resources s)) : Published s :=
  publishCommandWithResourcesAt codecs operation requirements (fun _ _ => pure ())
    (fun env => Native.commandAlgebra env) (fun _ => 422) binding

/-- Publish a query of an app with no accounts at an explicit route (GET allowed). -/
def assemblePublicQueryAt {s I O E} [IsSchema s] (codecs : Contract.Http.Codecs) (binding : RouteBinding)
    (operation : LeanApi.Core.Operation .query (fun _ => Unit) I O E)
    (requirements : operation.Requirements (Native.resources s)) : Published s :=
  publishQueryCheckedWithResourcesAt codecs operation requirements (fun _ _ => pure (.ok ()))
    Native.queryAlgebra (fun _ => 422) binding

end LeanApi.Native
