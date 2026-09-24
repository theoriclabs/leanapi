/-
  Endpoints over LeanDB programs (LAPI-02, read half).

  A handler may end in a LeanDB read program instead of an in-memory
  effect:

    def getUser (me : Auth Me) (id : Path Nat) : Read App (Except NotFound UserView)

  Its pure meaning is `Read.denote` over `DbState App`, so it is an ordinary
  `Handler (DbState App)`: the laws of `Endpoint.lean` (`Api.step_safe`,
  `Api.inductive_of`, `Api.noninterference`) apply to `DbApi.toApi`
  unchanged. Next to the meaning, `DbHandler` builds the *program* the
  runtime executes, with the law `prog_denote`: the program denotes exactly
  the meaning's response. Authentication is a read program too
  (`AuthenticatesDb`), so the whole request, authentication included, is
  one `Read`, run in one snapshot.

  `DbApi.service` runs each request's program with `Read.run` on a reader
  connection (one deferred snapshot). A `DbFault` answers without effect:
  503 for locking, 500 otherwise, logged with the request id.

  Write programs (`Txn s ε`) are LeanDB M14 part B. Until then there is no
  `DbHandler` for writes, so a `DbEndpoint` is always read-only.
-/
import LeanApi.Http.Endpoint
import LeanApi.Runtime.Blocking
import LeanDb

namespace LeanApi

open Lean LeanDb

/-! ## The meaning of a read program -/

instance {s : Type} [IsSchema s] [ToResponse ρ] : Handler (DbState s) (Read s ρ) where
  effect := .reads
  pathArity := 0
  inputs := []
  step p _ _ st _ := (ToResponse.toRes (Read.denote p st), st)
  errors _ _ _ _ := []
  step_safe _ _ _ _ _ _ := rfl
  Preserved _ _ := True
  step_preserved _ _ _ _ _ _ _ hs := hs
  ErrStable _ := True
  errors_stable _ _ _ _ _ _ _ _ := rfl
  Isolated R p := ∀ env r s₁ s₂, R env r s₁ s₂ →
    ToResponse.toRes (Read.denote p s₁) = ToResponse.toRes (Read.denote p s₂)
  step_isolated _ _ hI env r s₁ s₂ _ h := hI env r s₁ s₂ h

/-! ## Inputs that do not read the state -/

/-- Extraction does not depend on the state. Every input except `Auth`. -/
class FromRequest.Pure (σ : Type) (α : Type) [F : FromRequest σ α] : Prop where
  pure : ∀ s₁ s₂ env r, F.extract s₁ env r = F.extract s₂ env r

instance [FromQuery α] : FromRequest.Pure σ (Query α) := ⟨fun _ _ _ _ => rfl⟩
instance [FromParam α] : FromRequest.Pure σ (Header n α) := ⟨fun _ _ _ _ => rfl⟩
instance (priority := high) [FromParam α] : FromRequest.Pure σ (Header n (Option α)) :=
  ⟨fun _ _ _ _ => rfl⟩
instance [FromParam α] : FromRequest.Pure σ (IfMatch α) := ⟨fun _ _ _ _ => rfl⟩
instance [FromParam α] : FromRequest.Pure σ (IfMatchRequired α) := ⟨fun _ _ _ _ => rfl⟩
instance : FromRequest.Pure σ FreshToken := ⟨fun _ _ _ _ => rfl⟩
instance : FromRequest.Pure σ Now := ⟨fun _ _ _ _ => rfl⟩
instance (priority := high) [FromBody α] [FromForm α] : FromRequest.Pure σ (Body α) :=
  ⟨fun _ _ _ _ => rfl⟩
instance [FromBody α] : FromRequest.Pure σ (Body α) := ⟨fun _ _ _ _ => rfl⟩

/-! ## Authentication as a read program -/

/-- How to obtain an actor from a request by running a read program. The
    `Authenticates (DbState s) α` instance is its denotation, so the pure
    meaning and the executed program cannot disagree. -/
class AuthenticatesDb (s : Type) [IsSchema s] (α : Type) where
  challenge : String
  authProg : Env → Req → Read s (Except AuthFailure α)
  /-- Authentication reads credentials, not the router's path parameters. -/
  authProg_params : ∀ env r ps, authProg env { r with params := ps } = authProg env r := by
    intros; rfl

instance {s : Type} [IsSchema s] [A : AuthenticatesDb s α] : Authenticates (DbState s) α where
  challenge := A.challenge
  authenticate st env r := Read.denote (A.authProg env r) st
  authenticate_params st env r ps := by rw [A.authProg_params]

namespace AuthenticatesDb

/-- Which session token the request presents: a bearer token, else the
    cookie. The error is the answer when there is none; the string is the
    detail for a token the lookup refuses. -/
def sessionToken (req : Req) (cookie : Option String) : Except AuthFailure (String × String) :=
  let hasBearer := match req.header? "authorization" with
    | some v => ((v.trimAscii.toString.splitOn " ").headD "").toLower == "bearer"
    | none => false
  if hasBearer then
    match bearerToken? req with
    | none => .error (.invalid "malformed bearer token")
    | some t => .ok (t, "token rejected")
  else match cookie.bind req.cookie? with
    | some t => .ok (t, "session rejected")
    | none => .error .missing

/-- Session tokens looked up by a read program (`Authorization: Bearer`, and
    the cookie `cookie` when given). Same answers as
    `Authenticates.sessions`. -/
@[instance_reducible] def sessions {s : Type} [IsSchema s] (lookup : String → Read s (Option α))
    (cookie : Option String := none) (realm : String := "api") : AuthenticatesDb s α where
  challenge := s!"Bearer realm=\"{realm}\""
  authProg _ req :=
    match sessionToken req cookie with
    | .error e => pure (.error e)
    | .ok (t, rejected) => do
      match ← lookup t with
      | some a => pure (.ok a)
      | none => pure (.error (.invalid rejected))

/-- Basic credentials checked by a read program. Same answers as
    `Authenticates.passwords`. -/
@[instance_reducible] def passwords {s : Type} [IsSchema s] (verify : String → String → Read s (Option α))
    (realm : String := "api") : AuthenticatesDb s α where
  challenge := s!"Basic realm=\"{realm}\", charset=\"UTF-8\""
  authProg _ req :=
    let hasBasic := match req.header? "authorization" with
      | some v => ((v.trimAscii.toString.splitOn " ").headD "").toLower == "basic"
      | none => false
    if !hasBasic then pure (.error .missing) else
    match basicCredentials? req with
    | none => pure (.error (.invalid "malformed basic credentials"))
    | some (u, p) => do
      match ← verify u p with
      | some a => pure (.ok a)
      | none => pure (.error (.invalid "credentials rejected"))

end AuthenticatesDb

/-! ## Programs from handlers -/

/-- The read program a handler runs, with its law: it denotes exactly the
    response of the handler's pure meaning. Found by instance resolution
    over the arrows of `τ`, like `Handler`. -/
class DbHandler (s : Type) [IsSchema s] (τ : Type u) [H : Handler (DbState s) τ] where
  prog : τ → Env → Req → Nat → Read s Res
  /-- The field errors of all inputs, as a program. -/
  errorsProg : Env → Req → Nat → Read s (List FieldError)
  prog_denote : ∀ h env r st i, Read.denote (prog h env r i) st = (H.step h env r st i).1
  errors_denote : ∀ env r st i, Read.denote (errorsProg env r i) st = H.errors env r st i

private def invalidRes (es : List FieldError) : Res := (FieldError.problem es).toRes

instance {s : Type} [IsSchema s] [ToResponse ρ] : DbHandler s (Read s ρ) where
  prog p _ _ _ := ToResponse.toRes <$> p
  errorsProg _ _ _ := pure []
  prog_denote _ _ _ _ _ := rfl
  errors_denote _ _ _ _ := rfl

instance (priority := low) {s : Type} [IsSchema s] [ToResponse ρ] : DbHandler s ρ where
  prog a _ _ _ := pure (ToResponse.toRes a)
  errorsProg _ _ _ := pure []
  prog_denote _ _ _ _ _ := rfl
  errors_denote _ _ _ _ := rfl

instance {s : Type} [IsSchema s] {β : Type u} [FromParam α] [H : Handler (DbState s) β]
    [D : DbHandler s β] : DbHandler s (Path α → β) where
  prog f env r i :=
    match pathAt (α := α) r i with
    | .ok a => D.prog (f ⟨a⟩) env r (i + 1)
    | .error es => (fun more => invalidRes (es ++ more)) <$> D.errorsProg env r (i + 1)
  errorsProg env r i :=
    (fun more => (match pathAt (α := α) r i with | .ok _ => [] | .error es => es) ++ more) <$>
      D.errorsProg env r (i + 1)
  prog_denote f env r st i := by
    show _ = (match pathAt (α := α) r i with
      | .ok a => H.step (f ⟨a⟩) env r st (i + 1)
      | .error es => (invalidRes (es ++ H.errors env r st (i + 1)), st)).1
    cases pathAt (α := α) r i with
    | ok a => exact D.prog_denote _ env r st _
    | error es =>
      show invalidRes (es ++ Read.denote (D.errorsProg env r (i + 1)) st) = _
      rw [D.errors_denote]
  errors_denote env r st i := by
    show _ ++ Read.denote (D.errorsProg env r (i + 1)) st = _
    rw [D.errors_denote]; rfl

instance (priority := low) {s : Type} [IsSchema s] {β : Type u} [R' : FromRequest (DbState s) α]
    [FromRequest.Pure (DbState s) α] [H : Handler (DbState s) β] [D : DbHandler s β] :
    DbHandler s (α → β) where
  prog f env r i :=
    match R'.extract DbState.empty env r with
    | .ok a => D.prog (f a) env r i
    | .invalid es => (fun more => invalidRes (es ++ more)) <$> D.errorsProg env r i
    | .reject res => pure res
  errorsProg env r i :=
    (fun more => (match R'.extract DbState.empty env r with | .invalid es => es | _ => []) ++ more) <$>
      D.errorsProg env r i
  prog_denote f env r st i := by
    show _ = (match R'.extract st env r with
      | .ok a => H.step (f a) env r st i
      | .invalid es => (invalidRes (es ++ H.errors env r st i), st)
      | .reject res => (res, st)).1
    rw [FromRequest.Pure.pure (σ := DbState s) (α := α) st DbState.empty env r]
    cases R'.extract DbState.empty env r with
    | ok a => exact D.prog_denote _ env r st _
    | invalid es =>
      show invalidRes (es ++ Read.denote (D.errorsProg env r i) st) = _
      rw [D.errors_denote]
    | reject res => rfl
  errors_denote env r st i := by
    show _ ++ Read.denote (D.errorsProg env r i) st =
      (match R'.extract st env r with | .invalid es => es | _ => []) ++ H.errors env r st i
    rw [D.errors_denote, FromRequest.Pure.pure (σ := DbState s) (α := α) st DbState.empty env r]

instance {s : Type} [IsSchema s] {β : Type u} [A : AuthenticatesDb s α] [V : ViewOf (DbState s) α]
    [H : Handler (DbState s) β] [D : DbHandler s β] : DbHandler s (Auth α → β) where
  prog f env r i := do
    match ← A.authProg env r with
    | .ok who => D.prog (f ⟨who⟩) env r i
    | .error .missing => pure (unauthorized A.challenge)
    | .error (.invalid _) => pure (unauthorized A.challenge "invalid credentials")
  errorsProg := D.errorsProg
  prog_denote f env r st i := by
    show _ = (match Read.denote (A.authProg env r) st with
      | .ok who => H.step (f ⟨who⟩) env r st i
      | .error .missing => (unauthorized A.challenge, st)
      | .error (.invalid _) => (unauthorized A.challenge "invalid credentials", st)).1
    have hb : ∀ k : Except AuthFailure α → Read s Res,
        Read.denote (A.authProg env r >>= k) st = Read.denote (k (Read.denote (A.authProg env r) st)) st :=
      fun _ => rfl
    show Read.denote (A.authProg env r >>= _) st = _
    rw [hb]
    cases Read.denote (A.authProg env r) st with
    | ok who => exact D.prog_denote _ env r st _
    | error e => cases e <;> rfl
  errors_denote := D.errors_denote

/-! ## Endpoints that carry their program -/

/-- An endpoint over `DbState s`, together with the read program the runtime
    executes and the proof that it denotes the endpoint's response. -/
structure DbEndpoint (s : Type) [IsSchema s] extends Endpoint (DbState s) where
  prog : Env → Req → Read s Res
  prog_denote : ∀ env r st, Read.denote (prog env r) st = (toEndpoint.step env r st).1

namespace DbEndpoint

variable {s : Type} [IsSchema s]

def ofEndpoint {τ : Type u} (e : Endpoint (DbState s)) (h : τ) [H : Handler (DbState s) τ]
    [D : DbHandler s τ] (hstep : ∀ env r st, e.step env r st = H.step h env r st 0) : DbEndpoint s where
  toEndpoint := e
  prog env r := D.prog h env r 0
  prog_denote env r st := by rw [hstep]; exact D.prog_denote h env r st 0

def get {τ : Type u} (t : String) (h : τ) [H : Handler (DbState s) τ] [DbHandler s τ]
    (safe : H.effect.Safe := by endpoint_safe) : DbEndpoint s :=
  ofEndpoint (Endpoint.get t h safe) h fun _ _ _ => rfl

def head {τ : Type u} (t : String) (h : τ) [H : Handler (DbState s) τ] [DbHandler s τ]
    (safe : H.effect.Safe := by endpoint_safe) : DbEndpoint s :=
  ofEndpoint (Endpoint.head t h safe) h fun _ _ _ => rfl

def post {τ : Type u} (t : String) (h : τ) [Handler (DbState s) τ] [DbHandler s τ]
    (limit : Nat := 1024 * 1024) : DbEndpoint s :=
  ofEndpoint (Endpoint.post t h limit) h fun _ _ _ => rfl

def withSignature (e : DbEndpoint s) (sig : String) : DbEndpoint s :=
  { e with toEndpoint := e.toEndpoint.withSignature sig }

end DbEndpoint

/-! ## Runtime: reader connections and faults -/

/-- Read-only connections, each on its own worker thread, round-robin. -/
structure DbReaders where
  workers : Array Worker
  conns : Array Conn
  next : IO.Ref Nat

namespace DbReaders

/-- `n` read-only connections to an existing instance. -/
def «open» (path : System.FilePath) (n : Nat := 4) (queue : Nat := 1024) : IO DbReaders := do
  let mut conns := #[]
  for _ in [0:max n 1] do
    match ← openDbRaw path (readOnly := true) with
    | .ok c => conns := conns.push c
    | .error e => throw (IO.userError s!"open reader {path}: {e}")
  let workers ← conns.mapM fun _ => Worker.start queue
  return { workers, conns, next := ← IO.mkRef 0 }

def run (rd : DbReaders) (act : DbM α) : IO (Except SubmitError (Except DbError α)) := do
  let i ← rd.next.modifyGet fun i => (i, i + 1)
  let k := i % rd.conns.size
  match rd.workers[k]?, rd.conns[k]? with
  | some w, some c => w.run (DbM.run c act)
  | _, _ => return .error .stopped

def close (rd : DbReaders) : IO Unit := rd.workers.forM Worker.stop

end DbReaders

/-- A request that stopped on a fault has no effect. Locking is transient
    (503, retry); every other fault is the server's (500). No detail leaves
    the process. -/
def faultStatus : DbFault → Nat
  | .locking _ => 503
  | _ => 500

def faultRes (f : DbFault) (requestId : String) : Res :=
  let p := (Problem.make (faultStatus f)).withExt "request_id" (.str requestId)
  let p := if faultStatus f == 503 then p.withHeader "retry-after" "1" else p
  p.toRes

namespace DbEndpoint

variable {s : Type} [IsSchema s]

/-- Run against reader connections: a fresh environment, and the whole
    request (authentication, decoding, the handler) as one read program in
    one snapshot. -/
def toRoute (e : DbEndpoint s) (rd : DbReaders) (log : String → IO Unit) : Route where
  method := e.method
  template := e.template
  handler req := do
    let env ← Env.fresh
    let fault (f : DbFault) : IO Res := do
      log s!"\{\"event\":\"db_fault\",\"request_id\":\"{req.requestId}\",\"fault\":{(Json.str (toString f)).compress}}"
      return faultRes f req.requestId
    match ← rd.run (Read.run (e.prog env req)) with
    | .error .busy => fault (.locking "reader queue full")
    | .error .stopped => fault (.io "reader stopped")
    | .ok (.error err) => fault (DbFault.ofDbError err)
    | .ok (.ok (.error f)) => fault f
    | .ok (.ok (.ok res)) => return res
  bodyLimit := e.bodyLimit
  name := if e.signature.isEmpty then none else some e.signature

end DbEndpoint

/-! ## APIs over LeanDB -/

abbrev DbApi (s : Type) [IsSchema s] := List (DbEndpoint s)

namespace DbApi

variable {s : Type} [IsSchema s]

/-- The API's meaning: an ordinary typed API over `DbState s`, so
    `Api.step_safe`, `Api.inductive_of` and `Api.noninterference` apply. -/
def toApi (api : DbApi s) : Api (DbState s) := api.map (·.toEndpoint)

def describe (api : DbApi s) : String := api.toApi.describe

def routes (api : DbApi s) (rd : DbReaders) (log : String → IO Unit) : List Route :=
  api.map (·.toRoute rd log)

def service (api : DbApi s) (rd : DbReaders) (stack : Stack := {}) (log : String → IO Unit := IO.eprintln) :
    Service :=
  Service.ofRouter (Router.build! (api.routes rd log)) stack

/-- Every endpoint's program denotes its response. -/
theorem prog_denote (api : DbApi s) : ∀ e ∈ api, ∀ env r st,
    Read.denote (e.prog env r) st = (e.step env r st).1 :=
  fun e _ => e.prog_denote

end DbApi

/-! ## Compile-time checking: `dbapi!` -/

open Elab Term Meta in
/-- `dbapi! [e₁, e₂, …]`: `api!`'s checks (template syntax, path arity
    against the handler's `Path` arguments, route conflicts, the recorded
    signature) for endpoints over LeanDB programs. -/
elab "dbapi!" xs:term : term <= expectedType => do
  let e ← elabTerm xs (some expectedType)
  let e ← instantiateMVars e
  let mut items : Array Expr := #[]
  let mut l ← whnfR e
  repeat
    match l.getAppFnArgs with
    | (``List.cons, #[_, h, t]) => items := items.push h; l ← whnfR t
    | (``List.nil, _) => break
    | _ => throwError "dbapi!: expected a list literal"
  let mut keys : List (Method × String) := []
  let mut out : Array Expr := #[]
  for it in items do
    let ep ← mkAppM ``LeanApi.DbEndpoint.toEndpoint #[it]
    let m ← reduce (← mkAppM ``LeanApi.Endpoint.method #[ep])
    let t ← reduce (← mkAppM ``LeanApi.Endpoint.template #[ep])
    let n ← reduce (← mkAppM ``LeanApi.Endpoint.pathArity #[ep])
    if m.hasFVar || t.hasFVar || n.hasFVar || m.hasMVar || t.hasMVar || n.hasMVar then
      throwError "dbapi!: could not compute an endpoint's method, template and path arity statically"
    let mv ← unsafe evalExpr Method (mkConst ``LeanApi.Method) m
    let tv ← unsafe evalExpr String (mkConst ``String) t
    let nv ← unsafe evalExpr Nat (mkConst ``Nat) n
    -- `{s} [IsSchema s] {τ} (t) (h)`: τ is argument 2, h is argument 4.
    let ctors := [``LeanApi.DbEndpoint.get, ``LeanApi.DbEndpoint.head, ``LeanApi.DbEndpoint.post]
    let found := ctors.findSome? fun c =>
      (it.find? (·.isAppOf c)).bind fun app => (app.getAppArgs[2]?).bind fun τ =>
        (app.getAppArgs[4]?).map fun h => (τ, h)
    let (hName, sig) ← match found with
      | some (τ, h) =>
        let hName := match h.getAppFn.constName? with
          | some c => s!"`{c}`"
          | none => "the handler"
        pure (hName, toString (← ppExpr τ))
      | none => pure ("the handler", "")
    match parseTemplate tv with
    | .error msg => throwError "dbapi!: {mv} {tv}: {msg}"
    | .ok segs =>
      let k := (segs.filter fun | .lit _ => false | _ => true).length
      unless k == nv do
        throwError "dbapi!: {mv} {tv} has {k} path parameter(s), but {hName} takes {nv} `Path` argument(s):\n  {sig}"
    keys := keys ++ [(mv, tv)]
    out := out.push (← mkAppM ``LeanApi.DbEndpoint.withSignature #[it, toExpr sig])
  let errs := routeErrors keys
  unless errs.isEmpty do
    throwError m!"dbapi!: invalid routes:\n  {"\n  ".intercalate errs}"
  let elemTy := (← whnfR (← instantiateMVars expectedType)).appArg!
  mkListLit elemTy out.toList

end LeanApi
