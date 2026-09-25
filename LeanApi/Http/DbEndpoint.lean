/-
  Endpoints over LeanDB programs (LAPI-02).

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

  A handler may also end in a transaction, `Tx s ε ρ`: all or nothing,
  run on the writer under `BEGIN IMMEDIATE`; an abort with `e : ε` rolls
  back every write and answers `ToProblem ε`.
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

instance [FromQuery α] : FromRequest.Pure σ (QueryParams α) := ⟨fun _ _ _ _ => rfl⟩
instance [FromParam α] : FromRequest.Pure σ (Header n α) := ⟨fun _ _ _ _ => rfl⟩
instance [FromParam α] : FromRequest.Pure σ (QueryParam n α) := ⟨fun _ _ _ _ => rfl⟩
instance (priority := high) [FromParam α] : FromRequest.Pure σ (QueryParam n (Option α)) :=
  ⟨fun _ _ _ _ => rfl⟩
instance (priority := high) [FromParam α] : FromRequest.Pure σ (Header n (Option α)) :=
  ⟨fun _ _ _ _ => rfl⟩
instance [FromParam α] : FromRequest.Pure σ (IfMatch α) := ⟨fun _ _ _ _ => rfl⟩
instance [FromParam α] : FromRequest.Pure σ (IfMatchRequired α) := ⟨fun _ _ _ _ => rfl⟩
instance : FromRequest.Pure σ FreshToken := ⟨fun _ _ _ _ => rfl⟩
instance [LegacyFingerprint σ] : FromRequest.Pure σ Idempotency := ⟨fun _ _ _ _ => rfl⟩
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

end LeanApi

/-! ## Changing a transaction's failure type -/

namespace LeanDb.Txn
variable {σ s ε ε' : Type} [IsSchema s]
def mapErr (g : ε → ε') : {α : Type} → Txn σ s ε α → Txn σ s ε' α
  | _, .pure a => .pure a
  | _, .bind m f => .bind (mapErr g m) (fun a => mapErr g (f a))
  | _, .liftRead r => .liftRead r
  | _, @Txn.get _ _ _ _ α i h id => @Txn.get _ _ _ _ α i h id
  | _, @Txn.lookup _ _ _ _ α i1 i2 h ix k => @Txn.lookup _ _ _ _ α i1 i2 h ix k
  | _, .throw e => .throw (g e)
  | _, .orAbort m f => .orAbort (mapErr g m) (g ∘ f)
  | _, .orElse m h => .orElse (mapErr g m) (fun e => mapErr g (h e))
  | _, @Txn.insert _ _ _ _ α a b c h v => @Txn.insert _ _ _ _ α a b c h v
  | _, @Txn.update _ _ _ _ α a b c h o n => @Txn.update _ _ _ _ α a b c h o n
  | _, @Txn.set _ _ _ _ α a b c h r n => @Txn.set _ _ _ _ α a b c h r n
  | _, @Txn.patch _ _ _ _ α a b c h r fs n => @Txn.patch _ _ _ _ α a b c h r fs n
  | _, @Txn.append _ _ _ _ α a b h o n => @Txn.append _ _ _ _ α a b h o n
  | _, @Txn.delete _ _ _ _ α a b h id => @Txn.delete _ _ _ _ α a b h id

theorem denote_go_mapErr (g : ε → ε') (st0 : DbState s) {α : Type} (p : Txn σ s ε α) :
    ∀ st, denote.go st0 (mapErr g p) st =
      ((denote.go st0 p st).1.mapError g, (denote.go st0 p st).2) := by
  induction p with
  | pure a => intro st; rfl
  | bind m f ihm ihf =>
    intro st
    simp only [mapErr, denote.go, ihm]
    cases denote.go st0 m st with
    | mk r st' => cases r <;> simp [Except.mapError, ihf]
  | throw e => intro st; rfl
  | orAbort m f ih =>
    intro st
    simp only [mapErr, denote.go, ih]
    cases denote.go st0 m st with
    | mk r st' => rcases r with e | (e | a) <;> rfl
  | orElse m h ihm ihh =>
    intro st
    simp only [mapErr, denote.go, ihm]
    cases denote.go st0 m st with
    | mk r st' => rcases r with e | (e | a) <;> simp [Except.mapError, ihh]
  | _ => intro st; simp only [mapErr, denote.go]; (repeat' split) <;> rfl
end LeanDb.Txn

namespace LeanApi

open Lean LeanDb

/-! ## Write handlers: `Tx s ε ρ` -/

/-- A transaction program as a handler's result: all or nothing, failing
    with `ε`. Rank-2 in the transaction index, so `Current` rows cannot
    escape. The index is implicit: a handler's body is just `do …`. -/
abbrev Tx (s : Type) [IsSchema s] (ε ρ : Type) := {σ : Type} → Txn σ s ε ρ

/-- The meaning of a transaction handler: commit answers `ToResponse ρ`,
    abort answers `ToProblem ε` and restores the state (`Txn.denote`). -/
instance {s : Type} [IsSchema s] [ToResponse ρ] [ToProblem ε] : Handler (DbState s) (Tx s ε ρ) where
  effect := .writes
  pathArity := 0
  inputs := []
  step p _ _ st _ := (ToResponse.toRes (Txn.denote (p (σ := Unit)) st).1, (Txn.denote (p (σ := Unit)) st).2)
  errors _ _ _ _ := []
  step_safe h := h.elim
  Preserved I p := ∀ st, I st → I (Txn.denote (p (σ := Unit)) st).2
  step_preserved _ _ hp _ _ st _ hs := hp st hs
  ErrStable _ := True
  errors_stable _ _ _ _ _ _ _ _ := rfl
  Isolated R p := ∀ env r s₁ s₂, R env r s₁ s₂ →
    ToResponse.toRes (Txn.denote (p (σ := Unit)) s₁).1 = ToResponse.toRes (Txn.denote (p (σ := Unit)) s₂).1
  step_isolated _ _ hI env r s₁ s₂ _ h := hI env r s₁ s₂ h

/-! ## Programs, indexed by effect

The program a request runs has the shape its effect allows: a `Read` for
`pure`/`reads` (a reader connection, one snapshot) and a transaction for
`writes` (the writer, `BEGIN IMMEDIATE`). A transaction's abort value is
the response, so a refused request rolls back and still answers. -/

def DbProg (s : Type) [IsSchema s] : Effect → Type 1
  | .pure | .reads => Read s Res
  | .writes => {σ : Type} → Txn σ s Res Res

namespace DbProg

variable {s : Type} [IsSchema s]

def merge : Except Res Res → Res
  | .ok r => r
  | .error r => r

/-- The meaning: the response and the next state. -/
def denote : {e : Effect} → DbProg s e → DbState s → Res × DbState s
  | .pure, p, st => (Read.denote p st, st)
  | .reads, p, st => (Read.denote p st, st)
  | .writes, p, st => (merge (Txn.denote (p (σ := Unit)) st).1, (Txn.denote (p (σ := Unit)) st).2)

def ret : {e : Effect} → Res → DbProg s e
  | .pure, r => (pure r : Read s Res)
  | .reads, r => (pure r : Read s Res)
  | .writes, r => .pure r

/-- Read first, then continue with a program of the same effect. -/
def bindRead : {e : Effect} → Read s α → (α → DbProg s e) → DbProg s e
  | .pure, r, k => (r >>= k : Read s Res)
  | .reads, r, k => (r >>= k : Read s Res)
  | .writes, r, k => .bind (.liftRead r) (fun a => k a)

theorem denote_ret {e : Effect} (r : Res) (st : DbState s) : denote (ret (e := e) r) st = (r, st) := by
  cases e <;> rfl

theorem denote_bindRead {e : Effect} (r : Read s α) (k : α → DbProg s e) (st : DbState s) :
    denote (bindRead r k) st = denote (k (Read.denote r st)) st := by
  cases e
  · rfl
  · rfl
  · simp only [denote, bindRead, Txn.denote, Txn.denote.go]

end DbProg

/-! ## Programs from handlers -/

/-- The program a handler runs, with its law: it denotes exactly the
    handler's pure meaning, response *and* next state. Found by instance
    resolution over the arrows of `τ`, like `Handler`. -/
class DbHandler (s : Type) [IsSchema s] (τ : Type u) [H : Handler (DbState s) τ] where
  prog : τ → Env → Req → Nat → DbProg s H.effect
  /-- The field errors of all inputs, as a program. -/
  errorsProg : Env → Req → Nat → Read s (List FieldError)
  prog_denote : ∀ h env r st i, (prog h env r i).denote st = H.step h env r st i
  errors_denote : ∀ env r st i, Read.denote (errorsProg env r i) st = H.errors env r st i

private def invalidRes (es : List FieldError) : Res := (FieldError.problem es).toRes

instance {s : Type} [IsSchema s] [ToResponse ρ] : DbHandler s (Read s ρ) where
  prog p _ _ _ := (ToResponse.toRes <$> p : Read s Res)
  errorsProg _ _ _ := pure []
  prog_denote _ _ _ _ _ := rfl
  errors_denote _ _ _ _ := rfl

instance {s : Type} [IsSchema s] [ToResponse ρ] [ToProblem ε] : DbHandler s (Tx s ε ρ) where
  prog p _ _ _ :=
    .bind (Txn.mapErr (fun e => ToResponse.toRes (Except.error e : Except ε ρ)) p)
      (fun a => .pure (ToResponse.toRes (Except.ok a : Except ε ρ)))
  errorsProg _ _ _ := pure []
  prog_denote p env r st i := by
    show (DbProg.merge (Txn.denote _ st).1, (Txn.denote _ st).2) =
      (ToResponse.toRes (Txn.denote (p (σ := Unit)) st).1, (Txn.denote (p (σ := Unit)) st).2)
    simp only [Txn.denote, Txn.denote.go, Txn.denote_go_mapErr]
    cases Txn.denote.go st (p (σ := Unit)) st with
    | mk x st' => cases x <;> rfl
  errors_denote _ _ _ _ := rfl

instance (priority := low) {s : Type} [IsSchema s] [ToResponse ρ] : DbHandler s ρ where
  prog a _ _ _ := (pure (ToResponse.toRes a) : Read s Res)
  errorsProg _ _ _ := pure []
  prog_denote _ _ _ _ _ := rfl
  errors_denote _ _ _ _ := rfl

instance {s : Type} [IsSchema s] {β : Type u} [FromParam α] [H : Handler (DbState s) β]
    [D : DbHandler s β] : DbHandler s (Path α → β) where
  prog f env r i :=
    match pathAt (α := α) r i with
    | .ok a => D.prog (f ⟨a⟩) env r (i + 1)
    | .error es => DbProg.bindRead (D.errorsProg env r (i + 1)) fun more => DbProg.ret (invalidRes (es ++ more))
  errorsProg env r i :=
    (fun more => (match pathAt (α := α) r i with | .ok _ => [] | .error es => es) ++ more) <$>
      D.errorsProg env r (i + 1)
  prog_denote f env r st i := by
    show _ = (match pathAt (α := α) r i with
      | .ok a => H.step (f ⟨a⟩) env r st (i + 1)
      | .error es => (invalidRes (es ++ H.errors env r st (i + 1)), st))
    cases pathAt (α := α) r i with
    | ok a => exact D.prog_denote _ env r st _
    | error es =>
      show DbProg.denote (DbProg.bindRead _ _) st = _
      rw [DbProg.denote_bindRead, DbProg.denote_ret, D.errors_denote]
  errors_denote env r st i := by
    show _ ++ Read.denote (D.errorsProg env r (i + 1)) st = _
    rw [D.errors_denote]; rfl

instance (priority := low) {s : Type} [IsSchema s] {β : Type u} [R' : FromRequest (DbState s) α]
    [FromRequest.Pure (DbState s) α] [H : Handler (DbState s) β] [D : DbHandler s β] :
    DbHandler s (α → β) where
  prog f env r i :=
    match R'.extract DbState.empty env r with
    | .ok a => D.prog (f a) env r i
    | .invalid es => DbProg.bindRead (D.errorsProg env r i) fun more => DbProg.ret (invalidRes (es ++ more))
    | .reject res => DbProg.ret res
  errorsProg env r i :=
    (fun more => (match R'.extract DbState.empty env r with | .invalid es => es | _ => []) ++ more) <$>
      D.errorsProg env r i
  prog_denote f env r st i := by
    show _ = (match R'.extract st env r with
      | .ok a => H.step (f a) env r st i
      | .invalid es => (invalidRes (es ++ H.errors env r st i), st)
      | .reject res => (res, st))
    rw [FromRequest.Pure.pure (σ := DbState s) (α := α) st DbState.empty env r]
    cases R'.extract DbState.empty env r with
    | ok a => exact D.prog_denote _ env r st _
    | invalid es =>
      show DbProg.denote (DbProg.bindRead _ _) st = _
      rw [DbProg.denote_bindRead, DbProg.denote_ret, D.errors_denote]
    | reject res => exact DbProg.denote_ret res st
  errors_denote env r st i := by
    show _ ++ Read.denote (D.errorsProg env r i) st =
      (match R'.extract st env r with | .invalid es => es | _ => []) ++ H.errors env r st i
    rw [D.errors_denote, FromRequest.Pure.pure (σ := DbState s) (α := α) st DbState.empty env r]

instance {s : Type} [IsSchema s] {β : Type u} [A : AuthenticatesDb s α] [V : ViewOf (DbState s) α]
    [H : Handler (DbState s) β] [D : DbHandler s β] : DbHandler s (Auth α → β) where
  prog f env r i :=
    DbProg.bindRead (A.authProg env r) fun
      | .ok who => D.prog (f (Internal.authOf who)) env r i
      | .error .missing => DbProg.ret (unauthorized A.challenge)
      | .error (.invalid _) => DbProg.ret (unauthorized A.challenge "invalid credentials")
  errorsProg := D.errorsProg
  prog_denote f env r st i := by
    show DbProg.denote (DbProg.bindRead _ _) st = (match Read.denote (A.authProg env r) st with
      | .ok who => H.step (f (Internal.authOf who)) env r st i
      | .error .missing => (unauthorized A.challenge, st)
      | .error (.invalid _) => (unauthorized A.challenge "invalid credentials", st))
    rw [DbProg.denote_bindRead]
    cases Read.denote (A.authProg env r) st with
    | ok who => exact D.prog_denote _ env r st _
    | error e => cases e <;> exact DbProg.denote_ret _ st
  errors_denote := D.errors_denote

/-! ## Endpoints that carry their program -/

/-- An endpoint over `DbState s`, together with the program the runtime
    executes and the proof that it denotes the endpoint's meaning. -/
structure DbEndpoint (s : Type) [IsSchema s] extends Endpoint (DbState s) where
  prog : Env → Req → DbProg s toEndpoint.effect
  prog_denote : ∀ env r st, (prog env r).denote st = toEndpoint.step env r st

namespace DbEndpoint

variable {s : Type} [IsSchema s]

def get {τ : Type u} (t : String) (h : τ) [H : Handler (DbState s) τ] [D : DbHandler s τ]
    (safe : H.effect.Safe := by endpoint_safe) : DbEndpoint s where
  toEndpoint := Endpoint.get t h safe
  prog env r := D.prog h env r 0
  prog_denote env r st := D.prog_denote h env r st 0

def head {τ : Type u} (t : String) (h : τ) [H : Handler (DbState s) τ] [D : DbHandler s τ]
    (safe : H.effect.Safe := by endpoint_safe) : DbEndpoint s where
  toEndpoint := Endpoint.head t h safe
  prog env r := D.prog h env r 0
  prog_denote env r st := D.prog_denote h env r st 0

def post {τ : Type u} (t : String) (h : τ) [H : Handler (DbState s) τ] [D : DbHandler s τ]
    (limit : Nat := 1024 * 1024) : DbEndpoint s where
  toEndpoint := Endpoint.post t h limit
  prog env r := D.prog h env r 0
  prog_denote env r st := D.prog_denote h env r st 0

def put {τ : Type u} (t : String) (h : τ) [H : Handler (DbState s) τ] [D : DbHandler s τ]
    (limit : Nat := 1024 * 1024) : DbEndpoint s where
  toEndpoint := Endpoint.put t h limit
  prog env r := D.prog h env r 0
  prog_denote env r st := D.prog_denote h env r st 0

def patch {τ : Type u} (t : String) (h : τ) [H : Handler (DbState s) τ] [D : DbHandler s τ]
    (limit : Nat := 1024 * 1024) : DbEndpoint s where
  toEndpoint := Endpoint.patch t h limit
  prog env r := D.prog h env r 0
  prog_denote env r st := D.prog_denote h env r st 0

def delete {τ : Type u} (t : String) (h : τ) [H : Handler (DbState s) τ] [D : DbHandler s τ]
    (limit : Nat := 1024 * 1024) : DbEndpoint s where
  toEndpoint := Endpoint.delete t h limit
  prog env r := D.prog h env r 0
  prog_denote env r st := D.prog_denote h env r st 0

def withSignature (e : DbEndpoint s) (sig : String) : DbEndpoint s :=
  { e with toEndpoint := e.toEndpoint.withSignature sig }

end DbEndpoint

/-! ## Runtime: connections and faults -/

/-- One connection on its own worker thread. -/
structure DbWorker where
  worker : Worker
  conn : Conn

def DbWorker.run (w : DbWorker) (act : DbM α) : IO (Except SubmitError (Except DbError α)) :=
  w.worker.run (DbM.run w.conn act)

/-- The writer (one connection, `BEGIN IMMEDIATE`) and read-only
    connections, round-robin. -/
structure DbConns where
  writer : DbWorker
  readers : Array DbWorker
  next : IO.Ref Nat

namespace DbConns

/-- Open (creating, and verifying the schema of) the instance at `path`. -/
def «open» (path : System.FilePath) (specs : List TableSpec) (readers : Nat := 4) (queue : Nat := 1024) :
    IO DbConns := do
  let w ← match ← openDb path specs with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"open {path}: {e}")
  let mut rs := #[]
  for _ in [0:max readers 1] do
    match ← openDbRaw path (readOnly := true) with
    | .ok c => rs := rs.push { worker := ← Worker.start queue, conn := c }
    | .error e => throw (IO.userError s!"open reader {path}: {e}")
  return { writer := { worker := ← Worker.start queue, conn := w }, readers := rs, next := ← IO.mkRef 0 }

def read (dc : DbConns) (act : DbM α) : IO (Except SubmitError (Except DbError α)) := do
  let i ← dc.next.modifyGet fun i => (i, i + 1)
  match dc.readers[i % dc.readers.size]? with
  | some w => w.run act
  | none => return .error .stopped

def close (dc : DbConns) : IO Unit := do
  dc.readers.forM (·.worker.stop)
  dc.writer.worker.stop

end DbConns

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

namespace DbProg

variable {s : Type} [IsSchema s]

/-- Execute: reads on a reader in one snapshot, transactions on the
    writer under `BEGIN IMMEDIATE`. An abort rolls back and answers its
    response. -/
def exec (dc : DbConns) : {e : Effect} → DbProg s e → IO (Except DbFault Res)
  | .pure, p => runRead p
  | .reads, p => runRead p
  | .writes, p => do
    match ← dc.writer.run (Txn.run (s := s) p) with
    | .error .busy => return .error (.locking "writer queue full")
    | .error .stopped => return .error (.io "writer stopped")
    | .ok (.error err) => return .error (DbFault.ofDbError err)
    | .ok (.ok (.error f)) => return .error f
    | .ok (.ok (.ok x)) => return .ok (merge x)
where
  runRead (p : Read s Res) : IO (Except DbFault Res) := do
    match ← dc.read (Read.run p) with
    | .error .busy => return .error (.locking "reader queue full")
    | .error .stopped => return .error (.io "reader stopped")
    | .ok (.error err) => return .error (DbFault.ofDbError err)
    | .ok (.ok r) => return r

end DbProg

namespace DbEndpoint

variable {s : Type} [IsSchema s]

/-- A fresh environment, and the whole request (authentication, decoding,
    the handler) as one program: one snapshot, or one transaction. -/
def toRoute (e : DbEndpoint s) (dc : DbConns) (log : String → IO Unit) : Route where
  method := e.method
  template := e.template
  handler req := do
    let env ← Env.fresh
    let req := { req with params := req.params ++ Retry.routeParams e.method e.template e.inputs }
    match ← DbProg.exec dc (e.prog env req) with
    | .ok res => return res
    | .error f =>
      log s!"\{\"event\":\"db_fault\",\"request_id\":\"{req.requestId}\",\"fault\":{(Json.str (toString f)).compress}}"
      return faultRes f req.requestId
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

/-- The API's meaning, as for any typed API: route, then run the endpoint. -/
def step (api : DbApi s) (env : Env) (r : Req) (st : DbState s) : Res × DbState s :=
  api.toApi.step env r st

/-- The state after a sequence of requests. -/
def runAll (api : DbApi s) : List (Env × Req) → DbState s → DbState s
  | [], st => st
  | (env, r) :: rest, st => api.runAll rest (api.step env r st).2

def routes (api : DbApi s) (dc : DbConns) (log : String → IO Unit) : List Route :=
  api.map (·.toRoute dc log)

def service (api : DbApi s) (dc : DbConns) (stack : Stack := {}) (log : String → IO Unit := IO.eprintln) :
    Service :=
  Service.ofRouter (Router.build! (api.routes dc log)) stack

/-- Every endpoint's program denotes its meaning: the response and the
    next state. -/
theorem prog_denote (api : DbApi s) : ∀ e ∈ api, ∀ env r st,
    (e.prog env r).denote st = e.step env r st :=
  fun e _ => e.prog_denote

end DbApi

/-! ## Compile-time checking

`api!` checks lists of `DbEndpoint`s too (by the expected type). `dbapi!`
is its old name, kept for one release. -/

/-- Deprecated: write `api!`. -/
macro "dbapi!" xs:term : term => `(api! $xs)

end LeanApi
