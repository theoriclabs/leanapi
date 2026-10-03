import LeanApiDomain.Native

namespace LeanApi.Domain
open LeanApi LeanDb LeanApp.Domain

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

structure Context (s Profile : Type) [IsSchema s] [LeanApp.Domain.Entity Profile] : Type 1 where
  profile : LeanDb.Domain.EntityStorage s Profile
  store : Auth.Storage s Profile profile
  dc : DbConns
  cookies : Auth.CookieConfig
  fresh : IO Env := Env.fresh
  ttl : Nat := 86400
  dummyHash : String
  kdf : KDFGate

private def candidate {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (context : Context s Profile) (address : Email) : IO (Contract.CallResult (Option (String × Nat)) E) := do
  -- This preparation snapshot needs no decision clock. The operation clock is
  -- sampled exactly at final writer admission, after BEGIN IMMEDIATE.
  match ← context.dc.read (Read.runPrepared (pure ()) (fun _ => context.store.candidate address)) with
  | .error .busy => return .error (Native.fault "storage.busy" 503)
  | .error .stopped => return .error (Native.fault "storage.unavailable")
  | .ok (.error _) => return .error (Native.fault "storage.unavailable")
  | .ok (.ok (.error fault)) => return .error (Native.fault "storage.unavailable" (faultStatus fault))
  | .ok (.ok (.ok result)) => return result.mapError (Contract.CallError.mapDomain Empty.elim)

private def resolveRead {s Profile Actor Scope E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    [Native.ActorContext Actor Profile] (context : Context s Profile) (env : Env) (req : Req)
    (mutation : Bool) : Read s (Contract.CallResult (Actor Scope) E) :=
  Native.ActorContext.resolve context.store context.cookies env req mutation

private def resolveCommand {s Profile Actor Scope E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    [Native.ActorContext Actor Profile] (context : Context s Profile) (env : Env) (req : Req) :
    Native.CommandM Scope s E (Actor Scope) :=
  (Txn.ofRead (resolveRead context env req true)).orAbort id

/-- The milestone 1 RPC entry derived from an operation's name: literal POST envelope. -/
def rpcBinding (operation : LeanApp.Domain.Operation k Actor I O E) : RouteBinding :=
  RouteBinding.rpc { path := "/api/" ++ operation.contract.identity.namespaceName.toLower ++ "/" ++
      operation.contract.identity.name, maxBodyBytes := some 16384 }

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

private def probeRequest {s E A} [IsSchema s] (env : Env) :
    LeanApp.Domain.Request Unit E .command A (Native.resources s) → ExceptT Probe (Read s) A
  | .now => match Instant.ofEpochSeconds (Int.ofNat env.now) with
    | .ok now => pure now
    | .error _ => throw .stop
  | @RequestF.find _ _ _ _ _ _ storage reference =>
    match storage.find reference with
    | .ok program => liftM program
    | .error _ => throw .stop
  | @RequestF.findBy _ _ _ _ _ _ instanceT storage _ lookup key => do
    letI := instanceT
    match ← liftM (storage.findBy lookup key) with
    | .ok row => pure row
    | .error _ => throw .stop
  | @RequestF.select _ _ _ _ _ instanceT storage => do
    letI := instanceT
    match ← liftM storage.select with
    | .ok rows => pure rows
    | .error _ => throw .stop
  | @RequestF.linkField _ _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent =>
    match link.project targets column parent with
    | .error _ => throw .stop
    | .ok program => liftM program
  | @RequestF.verifyCredential _ _ _ _ _ _ instanceC credentials link subject _ => do
    letI := instanceC
    match subject with
    | none => throw (.verify none none)
    | some row => do
      match ← liftM (Native.storedHash (E := E) credentials link row.id) with
      | .ok stored => throw (.verify (some row.id.key) stored)
      | .error _ => throw .stop
  | _ => throw .stop

private def probeAlgebra {s E} [IsSchema s] (env : Env) :
    Algebra (ExceptT Probe (Read s)) .command Unit E (Native.resources s) := {
  request := fun request => do return .ok (← probeRequest env request)
  contains := fun _ _ => throw .stop
  project := fun _ => throw .stop
}

private def passwordField (fields : Lean.Json) (field : String) : Option Password :=
  match fields.getObjVal? field with
  | .ok (.str raw) => (LeanApp.Domain.Password.parse raw).toOption
  | _ => none

/-- Preparation before writer admission. Refused requests (Origin, credentials) do no KDF. -/
def prepareAuthored {s Profile Actor I O E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    [actorContext : Native.ActorContext Actor Profile] (context : Context s Profile)
    (operation : LeanApp.Domain.Operation .command Actor I O E)
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
        | .ok (.ok (.error fault)) => return .error (Native.fault "storage.unavailable" (faultStatus fault))
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
def assembleAuthoredAt {s Profile Actor I O E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    [actorContext : Native.ActorContext Actor Profile] (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (binding : RouteBinding) (operation : LeanApp.Domain.Operation .command Actor I O E)
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
      match ← Flow.run (Native.commandAlgebra env none context.ttl (some preparation))
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
def assembleCommandAt {s Profile Actor I O E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    [actorContext : Native.ActorContext Actor Profile] (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (binding : RouteBinding) (operation : LeanApp.Domain.Operation .command Actor I O E)
    (requirements : operation.Requirements (Native.resources s)) : Published s :=
  if operation.metadata.kdf.isEmpty && !operation.metadata.establishesSession then
    publishCommandWithResourcesAt codecs operation requirements (resolveCommand (Actor := Actor) context)
      (fun env => Native.commandAlgebra env) (fun _ => 422) binding
  else assembleAuthoredAt context codecs binding operation requirements

/-- Publish a generated query at an explicit route; GET is allowed only here. -/
def assembleQueryAt {s Profile Actor I O E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    [actorContext : Native.ActorContext Actor Profile] (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (binding : RouteBinding) (operation : LeanApp.Domain.Operation .query Actor I O E)
    (requirements : operation.Requirements (Native.resources s)) : Published s :=
  publishQueryCheckedWithResourcesAt codecs operation requirements
    (fun env req => resolveRead (Actor := Actor) context env req false) Native.queryAlgebra
    (fun _ => 422) binding

def assembleCommand {s Profile Actor I O E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    [Native.ActorContext Actor Profile] (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (operation : LeanApp.Domain.Operation .command Actor I O E)
    (requirements : operation.Requirements (Native.resources s)) : Published s :=
  assembleCommandAt context codecs (rpcBinding operation) operation requirements

def assembleQuery {s Profile Actor I O E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    [Native.ActorContext Actor Profile] (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (operation : LeanApp.Domain.Operation .query Actor I O E)
    (requirements : operation.Requirements (Native.resources s)) : Published s :=
  assembleQueryAt context codecs (rpcBinding operation) operation requirements

/-- Sign-up and sign-in. Browsers get the HttpOnly cookie and CSRF cookie after commit;
an explicit token request (`Accept: application/vnd.leanapp.token`) gets the raw token in
the body and no cookie. A presented live session, cookie or bearer, is rotated. -/
private def publishAuth {s Profile I E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (context : Context s Profile) (codecs : Contract.Http.Codecs) (binding : RouteBinding)
    (operation : LeanApp.Domain.Operation .command (fun _ => Unit) I (LeanApp.Domain.Ref Profile) E)
    (requirements : operation.Requirements (Native.resources s))
    (prepare : Req → I → IO (Contract.CallResult Auth.Admission E)) : Published s :=
  TrustedAdapter.preparedCommandAt codecs operation.contract prepare
    (fun env req input admission => do
      let tokenReply := Auth.tokenRequested req
      -- Validate any presented credential (cookie: Origin and CSRF too) in this snapshot.
      match ← Txn.ofRead (Auth.resolve (Scope := Unit) context.cookies env req context.store.live true) with
      | .error error => Txn.throw (error.mapDomain Empty.elim)
      | .ok _ => pure ()
      match Auth.anonymousGuard context.cookies req tokenReply with
      | .error error => Txn.throw (error.mapDomain Empty.elim)
      | .ok _ => pure ()
      -- Rotate the presented live session in this transaction. A later failure
      -- restores its validity together with all new profile/session writes.
      match Auth.presented context.cookies req with
      | .error error => Txn.throw (error.mapDomain Empty.elim)
      | .ok credential =>
        if let some token := credential.token? then context.store.revoke (Tokens.digest token)
      match ← Flow.run (Native.commandAlgebra env (some admission) context.ttl)
          (operation.bodyWithResources requirements () input) with
      | .error error => Txn.throw (.domain error)
      | .ok output =>
        let edits := if tokenReply then admission.prepared.tokenEdits
          else admission.prepared.replyEdits context.cookies context.ttl
        return (output, edits))
    (fun _ => 422) binding

private def authGuard {s Profile E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (context : Context s Profile) (req : Req) : Except (Contract.CallError E) Unit :=
  (Auth.anonymousGuard context.cookies req (Auth.tokenRequested req)).mapError
    (Contract.CallError.mapDomain Empty.elim)

def publishSignUpAt {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (context : Context s Profile) (codecs : Contract.Http.Codecs) (binding : RouteBinding)
    (account : Account Profile)
    (requirements : account.signUp.Requirements (Native.resources s)) : Published s :=
  publishAuth context codecs binding account.signUp requirements fun req input => do
    match authGuard context req with
    | .error error => return .error error
    | .ok _ => context.kdf.run (Auth.prepareSignUp (account.signUpPassword input))

def publishSignInAt {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (context : Context s Profile) (codecs : Contract.Http.Codecs) (binding : RouteBinding)
    (account : Account Profile)
    (requirements : account.signIn.Requirements (Native.resources s)) : Published s :=
  publishAuth context codecs binding account.signIn requirements fun req input => do
    match authGuard context req with
    | .error error => return .error error
    | .ok _ =>
      match ← candidate context (account.signInEmail input) with
      | .error error => return .error error
      | .ok credential => return ← context.kdf.run (Auth.prepareSignIn
          (account.signInEmail input) (account.signInPassword input) credential context.dummyHash)

def publishSignUp {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (context : Context s Profile) (codecs : Contract.Http.Codecs) (account : Account Profile)
    (requirements : account.signUp.Requirements (Native.resources s)) : Published s :=
  publishSignUpAt context codecs (rpcBinding account.signUp) account requirements

def publishSignIn {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (context : Context s Profile) (codecs : Contract.Http.Codecs) (account : Account Profile)
    (requirements : account.signIn.Requirements (Native.resources s)) : Published s :=
  publishSignInAt context codecs (rpcBinding account.signIn) account requirements

end LeanApi.Domain
