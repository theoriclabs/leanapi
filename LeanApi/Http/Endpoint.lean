/-
  Typed endpoints (docs/ENDPOINTS.md).

  An endpoint is a plain function whose type is its specification:

    def editNote (me : Auth User) (id : Path NoteId) (rev : IfMatch Rev) (edit : Body NoteEdit) :
        Writes State (Except EditError (Versioned NoteView))

  * Inputs are parameters; each parameter's type says where it comes from
    (`FromRequest σ α`, an open class; `Path` is positional).
  * The effect on state is `Reads σ` or `Writes σ`, or none.
  * Success shapes are `ToResponse α` (`Created`, `Versioned`, `Paged`,
    `NoContent`, JSON); failures are `Except ε` with `ToProblem ε`, whose
    status is typed as a 4xx/5xx.

  Every typed endpoint has a pure meaning, `Env → Req → σ → Res × σ`:
  randomness and time arrive in `Env`, authentication is a pure lookup over
  the state, and the runtime executes the whole request atomically against
  a `Store σ`. So a typed API is a `Props.Sys` (`Api.toSys`), and the
  property library applies to it directly.

  `Handler σ τ` computes, by instance resolution over the arrows of `τ`, the
  meaning of `τ` together with its laws: a safe handler never changes the
  state, and `Preserved I h` (an obligation computed from the signature:
  nothing for `Reads`, "`f` preserves `I`" for `Writes`) makes the handler
  preserve `I`. Hence, for every typed API:

  * `Api.step_safe`: GET and HEAD requests never change the state;
  * `Api.inductive_of`: an invariant holds in every reachable state once each
    endpoint's `Preserved` obligation is discharged.

  `api!` checks path arity against templates and route conflicts at compile
  time, and records each endpoint's elaborated signature.
-/
import LeanApi.Http.Router
import LeanApi.Http.Extract
import LeanApi.Http.Middleware
import LeanApi.Auth.Basic
import LeanApi.Auth.Jwt
import LeanApi.Util.Base64
import LeanApi.Runtime.Server
import LeanApi.Props.Sys
import LeanApi.Http.Idempotency
import Std.Sync.Mutex

namespace LeanApi

open Lean

/-! ## State backends -/

/-- Where an application's state lives. The framework only needs to read it
    and to modify it atomically; the in-memory mutex is one backend. -/
structure Store (σ : Type) where
  read : {α : Type} → (σ → α) → IO α
  modify : {α : Type} → (σ → σ × α) → IO α

/-- State in memory, under a mutex. -/
def Store.ofMutex (m : Std.Mutex σ) : Store σ where
  read f := m.atomically do return f (← get)
  modify f := m.atomically do
    let (s', a) := f (← get)
    set s'
    return a

/-! ## The environment: what a request may depend on besides its bytes -/

/-- Randomness and time, as inputs. The runtime draws a fresh `Env` for each
    request; the model quantifies over it. -/
structure Env where
  /-- Fresh random bytes for this request. -/
  entropy : ByteArray := .empty
  /-- Unix time in seconds. -/
  now : Nat := 0

/-- A fresh environment: 32 random bytes and the current time. -/
def Env.fresh : IO Env := do
  return { entropy := ← IO.getRandomBytes 32, now := ← Jwt.unixNow }

/-! ## Effects -/

/-- Reads the state; cannot change it. -/
def Reads (σ α : Type) := σ → α

/-- Changes the state: the new state and the answer. -/
def Writes (σ α : Type) := σ → σ × α

/-- What an endpoint may do to state, computed from its type. -/
inductive Effect where
  | pure | reads | writes
  deriving DecidableEq, Repr, Inhabited

/-- Safe methods (`GET`, `HEAD`) may only have these effects. -/
def Effect.Safe : Effect → Prop
  | .pure | .reads => True
  | .writes => False

instance : DecidablePred Effect.Safe := fun e => by cases e <;> unfold Effect.Safe <;> infer_instance

def Effect.label : Effect → String
  | .pure => "pure" | .reads => "reads" | .writes => "writes"

/-! ## Typed statuses -/

/-- A success status: 2xx, by type. -/
abbrev SuccessStatus := {n : Nat // 200 ≤ n ∧ n < 300}

/-- An error status: 4xx or 5xx, by type. -/
abbrev ErrorStatus := {n : Nat // 400 ≤ n ∧ n < 600}

/-! ## Inputs -/

/-- The next `{…}` parameter of the route template, decoded as `α`. -/
structure Path (α : Type) where
  val : α

/-- A value decoded from the query string (`FromQuery α`). Named
    `QueryParams` so it does not clash with `LeanDb.Query`. -/
structure QueryParams (α : Type) where
  val : α

/-- The old name of `QueryParams`, kept for one release. -/
@[deprecated QueryParams (since := "2026-09-23")] abbrev Query := QueryParams

/-- The request body, decoded as `α`: JSON (`FromBody α`), and also a form
    when `FromForm α` exists. -/
structure Body (α : Type) where
  val : α

/-- A header, decoded as `α`: required, or optional as `Header n (Option α)`. -/
structure Header (name : String) (α : Type) where
  val : α

/-- The `If-Match` precondition, when sent: the quoted ETag, decoded as
    `α`. `*` and absence are `none` (no precondition). -/
structure IfMatch (α : Type) where
  val : Option α

/-- A required `If-Match` precondition: 428 when missing. -/
structure IfMatchRequired (α : Type) where
  val : α

/-- The authenticated actor, of the type the scheme produces.

    The constructor is private: an `Auth α` is made only by authentication
    (the `FromRequest` and `Handler` instances below, and `DbEndpoint`'s
    through `Internal.authOf`). Application code cannot write
    `⟨otherUser⟩ : Auth UserId`, so a handler, or a row-policy view built
    from `me`, acts for the caller the request authenticated and no one else.
    `scripts/check_private_escapes.sh` (CI) refuses any use of
    `LeanApi.Internal` outside `LeanApi/` and `tests/`. -/
structure Auth (α : Type) where
  private mk ::
  val : α

/-! Framework internals. Lean 4 has no friend modules, so the framework's
    other files reach private constructors through this namespace, and CI
    (`scripts/check_private_escapes.sh`) refuses its use anywhere else. -/
namespace Internal

/-- An `Auth` for an actor that authentication has produced. For the
    framework's authentication paths only (`DbEndpoint`). -/
def authOf (who : α) : Auth α := ⟨who⟩

end Internal

/-- A fresh random token (24 bytes of the request's entropy, base64url):
    randomness as an input. -/
structure FreshToken where
  val : String

/-- The request's time (Unix seconds). -/
structure Now where
  val : Nat

instance : CoeHead (Path α) α := ⟨Path.val⟩
instance : CoeHead (QueryParams α) α := ⟨QueryParams.val⟩
instance : CoeHead (Body α) α := ⟨Body.val⟩
instance : CoeHead (Header n α) α := ⟨Header.val⟩
instance : CoeHead (Auth α) α := ⟨Auth.val⟩
instance : CoeHead FreshToken String := ⟨FreshToken.val⟩

/-- The outcome of extracting one input. -/
inductive Got (α : Type) where
  | ok (a : α)
  /-- Field errors, reported together with the other parameters' (422). -/
  | invalid (es : List FieldError)
  /-- A final answer (401, 415, 400). -/
  | reject (r : Res)

def Got.map (f : α → β) : Got α → Got β
  | .ok a => .ok (f a)
  | .invalid es => .invalid es
  | .reject r => .reject r

def Got.ofDecoded : Decoded α → Got α
  | .ok a => .ok a
  | .error es => .invalid es

/-- A relation between two runs of one request, on the request and the two
    states: what isolation is stated against. -/
abbrev Rel (σ : Type) := Env → Req → σ → σ → Prop

/-- How to obtain an input of type `α` from a request, given the state and
    the environment. Pure. Open: apps add their own instances. `kind`
    names the source, for `Api.describe`. -/
class FromRequest (σ : Type) (α : Type) where
  kind : String
  extract : σ → Env → Req → Got α

/-- Extraction gives the same result in `R`-related states. Holds by `rfl`
    for every input that does not read the state. -/
def FromRequest.Stable (R : Rel σ) [F : FromRequest σ α] : Prop :=
  ∀ env r s₁ s₂, R env r s₁ s₂ → F.extract s₁ env r = F.extract s₂ env r

/-- A record from the query string. -/
class FromQuery (α : Type) where
  fromQuery : Extract α

/-- A record from a form body. -/
class FromForm (α : Type) where
  fromForm : List (String × String) → Decoded α

/-- How to obtain an actor of type `α`: a pure check of the request against
    the state and the environment (e.g. the time, for JWT expiry). -/
class Authenticates (σ : Type) (α : Type) where
  challenge : String
  authenticate : σ → Env → Req → Except AuthFailure α
  /-- Authentication reads credentials, not the router's path parameters. -/
  authenticate_params : ∀ s env r ps, authenticate s env { r with params := ps } = authenticate s env r := by
    intros; rfl

/-- What actor `a` may observe: two states look the same to `a`. Used by
    `Api.noninterference`. Without an instance, the default makes every
    difference observable (and so claims nothing). -/
class ViewOf (σ : Type) (α : Type) where
  same : α → σ → σ → Prop

instance (priority := low) : ViewOf σ α := ⟨fun _ s₁ s₂ => s₁ = s₂⟩


namespace Authenticates

/-- Session tokens looked up in the state: `Authorization: Bearer`, and the
    cookie `cookie` when given. -/
def sessions (lookup : σ → String → Option α) (cookie : Option String := none) (realm : String := "api") :
    Authenticates σ α where
  challenge := s!"Bearer realm=\"{realm}\""
  authenticate s _ req :=
    let hasBearer := match req.header? "authorization" with
      | some v => ((v.trimAscii.toString.splitOn " ").headD "").toLower == "bearer"
      | none => false
    if hasBearer then
      match bearerToken? req with
      | none => .error (.invalid "malformed bearer token")
      | some t => match lookup s t with
        | some a => .ok a
        | none => .error (.invalid "token rejected")
    else match cookie.bind req.cookie? with
      | some t => match lookup s t with
        | some a => .ok a
        | none => .error (.invalid "session rejected")
      | none => .error .missing

/-- Basic credentials checked against the state. -/
def passwords (verify : σ → String → String → Option α) (realm : String := "api") : Authenticates σ α where
  challenge := s!"Basic realm=\"{realm}\", charset=\"UTF-8\""
  authenticate s _ req :=
    let hasBasic := match req.header? "authorization" with
      | some v => ((v.trimAscii.toString.splitOn " ").headD "").toLower == "basic"
      | none => false
    if !hasBasic then .error .missing else
    match basicCredentials? req with
    | none => .error (.invalid "malformed basic credentials")
    | some (u, p) => match verify s u p with
      | some a => .ok a
      | none => .error (.invalid "credentials rejected")

/-- HS256 JWTs, verified at the request's time; claims mapped to an actor
    against the state. -/
def jwt (policy : Jwt.Policy) (toActor : σ → Json → Option α) (realm : String := "api") : Authenticates σ α where
  challenge := s!"Bearer realm=\"{realm}\""
  authenticate s env req :=
    match req.header? "authorization" with
    | none => .error .missing
    | some v =>
      if ((v.trimAscii.toString.splitOn " ").headD "").toLower != "bearer" then .error .missing else
      match bearerToken? req with
      | none => .error (.invalid "malformed bearer token")
      | some tok => match Jwt.verify policy env.now tok with
        | .error _ => .error (.invalid "token rejected")
        | .ok claims => match toActor s claims with
          | some a => .ok a
          | none => .error (.invalid "unknown subject")

end Authenticates

instance [FromQuery α] : FromRequest σ (QueryParams α) where
  kind := "query"
  extract _ _ r := (Got.ofDecoded (FromQuery.fromQuery r)).map QueryParams.mk

instance [FromParam α] : FromRequest σ (Header n α) where
  kind := s!"header {n}"
  extract _ _ r := (Got.ofDecoded (Extract.header (α := α) n r)).map Header.mk

instance (priority := high) [FromParam α] : FromRequest σ (Header n (Option α)) where
  kind := s!"header {n}?"
  extract _ _ r := (Got.ofDecoded (Extract.headerOpt (α := α) n r)).map Header.mk

/-- Strip the quotes of an entity tag (`"3"`, `W/"3"`). -/
def unquoteETag (s : String) : String :=
  let s := s.trimAscii.toString
  let s := if s.startsWith "W/" then (s.drop 2).toString else s
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then ((s.drop 1).dropEnd 1).toString else s

instance [FromParam α] : FromRequest σ (IfMatch α) where
  kind := "if-match"
  extract _ _ r :=
    match r.header? "if-match" with
    | none => .ok ⟨none⟩
    | some v =>
      if v.trimAscii.toString == "*" then .ok ⟨none⟩ else
      match FromParam.fromParam (α := α) (unquoteETag v) with
      | .ok a => .ok ⟨some a⟩
      | .error m => .invalid [⟨"header.if-match", m⟩]

instance [FromParam α] : FromRequest σ (IfMatchRequired α) where
  kind := "if-match (required)"
  extract _ _ r :=
    match r.header? "if-match" with
    | none => .reject (Problem.make 428 (some "If-Match with the resource's ETag is required")).toRes
    | some v =>
      match FromParam.fromParam (α := α) (unquoteETag v) with
      | .ok a => .ok ⟨a⟩
      | .error m => .invalid [⟨"header.if-match", m⟩]

instance [A : Authenticates σ α] : FromRequest σ (Auth α) where
  kind := "auth"
  extract s env r :=
    match A.authenticate s env r with
    | .ok who => .ok ⟨who⟩
    | .error .missing => .reject (unauthorized A.challenge)
    | .error (.invalid _) => .reject (unauthorized A.challenge "invalid credentials")

/-- The request's `Idempotency-Key`, with the retry identity the framework
    computes for it (`Retry`): the endpoint, and a fingerprint of the request
    as the endpoint reads it. Handlers never build a fingerprint. -/
structure Idempotency where
  retry : Option Retry

instance [L : LegacyFingerprint σ] : FromRequest σ Idempotency where
  kind := "idempotency"
  extract _ _ r :=
    match r.header? "idempotency-key" with
    | none => .ok ⟨none⟩
    | some k =>
      if Retry.validKey k then .ok ⟨some (Retry.ofReq (Retry.opOf r) (Retry.declaredOf r) k r (L.v0 r))⟩
      else .invalid [⟨"header.idempotency-key", "1–255 visible ASCII characters"⟩]

instance : FromRequest σ FreshToken where
  kind := "fresh token"
  extract _ env _ := .ok ⟨Base64.encodeUrl (env.entropy.extract 0 24)⟩

instance : FromRequest σ Now where
  kind := "now"
  extract _ env _ := .ok ⟨env.now⟩

private def bodyParseFailure (es : List FieldError) : Bool :=
  es.any fun e => e.loc == "body" &&
    (e.msg.startsWith "invalid JSON" || e.msg == "body is not UTF-8" || e.msg == "invalid form encoding")

private def classify (d : Decoded α) : Got α :=
  match d with
  | .ok a => .ok a
  | .error es => if bodyParseFailure es then .reject (FieldError.problem es 400).toRes else .invalid es

private def unsupported (types : List String) : Res :=
  ((Problem.make 415 (some s!"expected {", ".intercalate types}")).withHeader "accept-post"
    (", ".intercalate types)).toRes

private def jsonType := "application/json"
private def formType := "application/x-www-form-urlencoded"

/-- A body accepted as JSON or as a form. -/
instance (priority := high) [FromBody α] [FromForm α] : FromRequest σ (Body α) where
  kind := "body (json or form)"
  extract _ _ r :=
    match r.contentType? with
    | some ct =>
      if ct == jsonType then (classify (Extract.json (α := α) r)).map Body.mk
      else if ct == formType then
        (classify (do FromForm.fromForm (← Extract.formPairs r))).map Body.mk
      else .reject (unsupported [jsonType, formType])
    | none => .reject (unsupported [jsonType, formType])

/-- A JSON body. -/
instance [FromBody α] : FromRequest σ (Body α) where
  kind := "body (json)"
  extract _ _ r :=
    match r.contentType? with
    | some ct => if ct == jsonType then (classify (Extract.json (α := α) r)).map Body.mk
                 else .reject (unsupported [jsonType])
    | none => .reject (unsupported [jsonType])

/-! ## Records -/

/-- Fields of a JSON object, decoded with their own locations; errors from
    independent fields accumulate. -/
def Fields (α : Type) := String → Json → Decoded α

namespace Fields

instance : Functor Fields where
  map f x := fun loc j => (x loc j).map f

instance : Pure Fields := ⟨fun a _ _ => .ok a⟩

instance : Seq Fields where
  seq f x := fun loc j => (both (f loc j) (x () loc j)).map fun (g, a) => g a

instance : Applicative Fields := {}

/-- A required field. -/
def req [FromBody α] (name : String) : Fields α := fun loc j => field loc j name
/-- An optional field (missing or `null` is `none`). -/
def opt [FromBody α] (name : String) : Fields (Option α) := fun loc j => fieldOpt loc j name
/-- An optional field with a default. -/
def dflt [FromBody α] (name : String) (d : α) : Fields α := fun loc j => fieldD loc j name d

end Fields

/-- A `FromBody` instance from a record of fields. -/
def FromBody.record (f : Fields α) : FromBody α where
  fromBody loc j := match j with
    | .obj _ => f loc j
    | _ => .error [⟨loc, "expected an object"⟩]

/-- Fields of a form body. -/
def FormFields (α : Type) := List (String × String) → Decoded α

namespace FormFields

instance : Functor FormFields where
  map f x := fun ps => (x ps).map f

instance : Pure FormFields := ⟨fun a _ => .ok a⟩

instance : Seq FormFields where
  seq f x := fun ps => (both (f ps) (x () ps)).map fun (g, a) => g a

instance : Applicative FormFields := {}

private def decodeAt [FromParam α] (loc : String) (s : String) : Decoded α :=
  match FromParam.fromParam s with
  | .ok a => .ok a
  | .error m => .error [⟨loc, m⟩]

def req [FromParam α] (name : String) : FormFields α := fun ps =>
  match ps.lookup name with
  | some s => decodeAt s!"body.{name}" s
  | none => .error [⟨s!"body.{name}", "field required"⟩]

def opt [FromParam α] (name : String) : FormFields (Option α) := fun ps =>
  match ps.lookup name with
  | some s => (decodeAt s!"body.{name}" s).map some
  | none => .ok none

end FormFields

def FromForm.record (f : FormFields α) : FromForm α := ⟨f⟩

/-! ## Outputs -/

/-- How a success value answers. -/
class ToResponse (α : Type) where
  toRes : α → Res

/-- Any JSON value answers 200. -/
instance (priority := low) [ToJson α] : ToResponse α := ⟨fun a => Res.ok a⟩

/-- How a failure answers: a typed error status (never 2xx) and an optional
    detail, rendered as RFC 9457 `problem+json`. -/
class ToProblem (ε : Type) where
  status : ε → ErrorStatus
  detail : ε → Option String := fun _ => none
  /-- Extension members of the problem object (RFC 9457 §3.2). -/
  extensions : ε → List (String × Json) := fun _ => []

def ToProblem.problem [ToProblem ε] (e : ε) : Problem :=
  (ToProblem.extensions e).foldl (fun p (k, v) => p.withExt k v)
    (Problem.make (ToProblem.status e).1 (ToProblem.detail e))

/-- Field errors as a failure: 422, as the extractors report them. -/
instance : ToProblem (List FieldError) where
  status _ := ⟨422, by decide⟩
  detail _ := some "request validation failed"
  extensions es := [("errors", Json.arr (es.map FieldError.toJson).toArray)]

instance [ToResponse α] [ToProblem ε] : ToResponse (Except ε α) where
  toRes
    | .ok a => ToResponse.toRes a
    | .error e => (ToProblem.problem e).toRes

/-- The resource does not exist, or the caller may not know it does. -/
structure NotFound where
  deriving Repr, Inhabited

instance : ToProblem NotFound where
  status _ := ⟨404, by decide⟩

/-- A newly created resource: 201, with `Location` when given. -/
structure Created (α : Type) where
  val : α
  location : Option String := none

instance [ToResponse α] : ToResponse (Created α) where
  toRes c :=
    let r := { ToResponse.toRes c.val with status := (⟨201, by decide⟩ : SuccessStatus).1 }
    match c.location with
    | some l => r.setHeader "location" l
    | none => r

/-- A value with a version: adds `ETag: "<version>"`. -/
structure Versioned (α : Type) where
  val : α
  version : Nat

instance [ToResponse α] : ToResponse (Versioned α) where
  toRes v := (ToResponse.toRes v.val).setHeader "etag" s!"\"{v.version}\""

/-- No body: 204. -/
structure NoContent where
  deriving Repr, Inhabited

instance : ToResponse NoContent := ⟨fun _ => Res.empty (⟨204, by decide⟩ : SuccessStatus).1⟩

/-- One page of a collection. -/
structure Paged (α : Type) where
  items : List α
  total : Nat
  page : Nat

instance [ToJson α] : ToResponse (Paged α) where
  toRes p := Res.ok (Json.mkObj [("items", Json.arr (p.items.map toJson).toArray),
    ("total", Json.num p.total), ("page", Json.num p.page)])

/-- Plain text. -/
structure Text where
  val : String

instance : ToResponse Text := ⟨fun t => Res.text t.val⟩

/-- A value answered together with a cookie. -/
structure WithCookie (α : Type) where
  val : α
  cookie : Res.Cookie

instance [ToResponse α] : ToResponse (WithCookie α) where
  toRes w := (ToResponse.toRes w.val).setCookie w.cookie

/-! ## Handlers: a function type as a request specification -/

private def validationRes (es : List FieldError) : Res := (FieldError.problem es).toRes

/-- `τ` is a handler: an arrow of inputs ending in an effect and a response.
    Instance resolution computes its meaning and metadata, and proves its
    laws. -/
class Handler (σ : Type) (τ : Type u) where
  effect : Effect
  pathArity : Nat
  inputs : List String
  /-- The pure meaning, given the index of the next `Path` parameter. -/
  step : τ → Env → Req → σ → Nat → Res × σ
  /-- The field errors of all inputs, without running the handler. -/
  errors : Env → Req → σ → Nat → List FieldError
  /-- A safe handler never changes the state. -/
  step_safe : effect.Safe → ∀ h env r s i, (step h env r s i).2 = s
  /-- What preserving `I` requires of a handler of this type: nothing for
      `Reads`; that the state function preserves `I` for `Writes`. -/
  Preserved : (σ → Prop) → τ → Prop
  step_preserved : ∀ I h, Preserved I h → ∀ env r s i, I s → I (step h env r s i).2
  /-- Every input's extraction is stable under `R`. -/
  ErrStable : Rel σ → Prop
  errors_stable : ∀ R, ErrStable R → ∀ env r s₁ s₂ i, R env r s₁ s₂ → errors env r s₁ i = errors env r s₂ i
  /-- What isolation under `R` requires of a handler of this type. `Auth`
      narrows `R` to the authenticated actor's view (`ViewOf`); `Reads` and
      `Writes` require the response to be equal in related states. -/
  Isolated : Rel σ → τ → Prop
  step_isolated : ∀ R h, Isolated R h → ∀ env r s₁ s₂ i, R env r s₁ s₂ →
    (step h env r s₁ i).1 = (step h env r s₂ i).1

/-- The `i`th path parameter, decoded. -/
def pathAt [FromParam α] (r : Req) (i : Nat) : Decoded α :=
  match r.params[i]? with
  | some (n, v) =>
    match FromParam.fromParam v with
    | .ok a => .ok a
    | .error m => .error [⟨s!"path.{n}", m⟩]
  | none => .error [⟨s!"path[{i}]", "missing path parameter"⟩]

instance {β : Type u} [FromParam α] [H : Handler σ β] : Handler σ (Path α → β) where
  effect := H.effect
  pathArity := H.pathArity + 1
  inputs := "path" :: H.inputs
  step f env r s i :=
    match pathAt (α := α) r i with
    | .ok a => H.step (f ⟨a⟩) env r s (i + 1)
    | .error es => (validationRes (es ++ H.errors env r s (i + 1)), s)
  errors env r s i :=
    (match pathAt (α := α) r i with | .ok _ => [] | .error es => es) ++ H.errors env r s (i + 1)
  step_safe hs f env r s i := by
    split
    · exact H.step_safe hs _ env r s _
    · rfl
  Preserved I f := ∀ a, H.Preserved I (f ⟨a⟩)
  step_preserved I f hp env r s i hs := by
    split
    · exact H.step_preserved I _ (hp _) env r s _ hs
    · exact hs
  ErrStable R := H.ErrStable R
  errors_stable R hR env r s₁ s₂ i h := by
    rw [H.errors_stable R hR env r s₁ s₂ (i + 1) h]
  Isolated R f := H.ErrStable R ∧ ∀ a, H.Isolated R (f ⟨a⟩)
  step_isolated R f hI env r s₁ s₂ i h := by
    cases pathAt (α := α) r i with
    | ok a => exact H.step_isolated R _ (hI.2 a) env r s₁ s₂ _ h
    | error es => simp only [H.errors_stable R hI.1 env r s₁ s₂ (i + 1) h]

instance (priority := low) {β : Type u} [R' : FromRequest σ α] [H : Handler σ β] : Handler σ (α → β) where
  effect := H.effect
  pathArity := H.pathArity
  inputs := R'.kind :: H.inputs
  step f env r s i :=
    match R'.extract s env r with
    | .ok a => H.step (f a) env r s i
    | .invalid es => (validationRes (es ++ H.errors env r s i), s)
    | .reject res => (res, s)
  errors env r s i :=
    (match R'.extract s env r with | .invalid es => es | _ => []) ++ H.errors env r s i
  step_safe hs f env r s i := by
    split
    · exact H.step_safe hs _ env r s _
    · rfl
    · rfl
  Preserved I f := ∀ a, H.Preserved I (f a)
  step_preserved I f hp env r s i hs := by
    split
    · exact H.step_preserved I _ (hp _) env r s _ hs
    · exact hs
    · exact hs
  ErrStable R := FromRequest.Stable (α := α) R ∧ H.ErrStable R
  errors_stable R hR env r s₁ s₂ i h := by
    rw [hR.1 env r s₁ s₂ h, H.errors_stable R hR.2 env r s₁ s₂ i h]
  Isolated R f := FromRequest.Stable (α := α) R ∧ H.ErrStable R ∧ ∀ a, H.Isolated R (f a)
  step_isolated R f hI env r s₁ s₂ i h := by
    rw [← hI.1 env r s₁ s₂ h]
    cases R'.extract s₁ env r with
    | ok a => exact H.step_isolated R _ (hI.2.2 a) env r s₁ s₂ _ h
    | invalid es => simp only [H.errors_stable R hI.2.1 env r s₁ s₂ i h]
    | reject res => rfl

/-- `Auth α → β`: authenticate, then run `β` with the actor. For isolation,
    the relation narrows to what the authenticated actor may see. -/
instance {β : Type u} [A : Authenticates σ α] [V : ViewOf σ α] [H : Handler σ β] : Handler σ (Auth α → β) where
  effect := H.effect
  pathArity := H.pathArity
  inputs := "auth" :: H.inputs
  step f env r s i :=
    match A.authenticate s env r with
    | .ok who => H.step (f ⟨who⟩) env r s i
    | .error .missing => (unauthorized A.challenge, s)
    | .error (.invalid _) => (unauthorized A.challenge "invalid credentials", s)
  errors env r s i := H.errors env r s i
  step_safe hs f env r s i := by
    split
    · exact H.step_safe hs _ env r s _
    · rfl
    · rfl
  -- The obligations quantify over `Auth α` values: a proof receives the
  -- actor and never constructs one (the constructor is private).
  Preserved I f := ∀ a : Auth α, H.Preserved I (f a)
  step_preserved I f hp env r s i hs := by
    split
    · exact H.step_preserved I _ (hp ⟨_⟩) env r s _ hs
    · exact hs
    · exact hs
  ErrStable R := H.ErrStable R
  errors_stable R hR env r s₁ s₂ i h := H.errors_stable R hR env r s₁ s₂ i h
  Isolated R f :=
    (∀ env r s₁ s₂, R env r s₁ s₂ → A.authenticate s₁ env r = A.authenticate s₂ env r) ∧
    (∀ env r s₁ s₂ a, R env r s₁ s₂ → A.authenticate s₁ env r = .ok a → V.same a s₁ s₂) ∧
    ∀ a : Auth α, H.Isolated (fun env r s₁ s₂ => R env r s₁ s₂ ∧ V.same a.val s₁ s₂) (f a)
  step_isolated R f hI env r s₁ s₂ i h := by
    rw [← hI.1 env r s₁ s₂ h]
    cases ha : A.authenticate s₁ env r with
    | ok a => exact H.step_isolated _ _ (hI.2.2 ⟨a⟩) env r s₁ s₂ _ ⟨h, hI.2.1 env r s₁ s₂ a h ha⟩
    | error e => cases e <;> rfl

instance [ToResponse ρ] : Handler σ (Reads σ ρ) where
  effect := .reads
  pathArity := 0
  inputs := []
  step f _ _ s _ := (ToResponse.toRes (f s), s)
  errors _ _ _ _ := []
  step_safe _ _ _ _ _ _ := rfl
  Preserved _ _ := True
  step_preserved _ _ _ _ _ _ _ hs := hs
  ErrStable _ := True
  errors_stable _ _ _ _ _ _ _ _ := rfl
  Isolated R f := ∀ env r s₁ s₂, R env r s₁ s₂ → ToResponse.toRes (f s₁) = ToResponse.toRes (f s₂)
  step_isolated _ _ hI env r s₁ s₂ _ h := hI env r s₁ s₂ h

instance [ToResponse ρ] : Handler σ (Writes σ ρ) where
  effect := .writes
  pathArity := 0
  inputs := []
  step f _ _ s _ := ((ToResponse.toRes (f s).2), (f s).1)
  errors _ _ _ _ := []
  step_safe h := h.elim
  Preserved I f := ∀ s, I s → I (f s).1
  step_preserved _ _ hp _ _ s _ hs := hp s hs
  ErrStable _ := True
  errors_stable _ _ _ _ _ _ _ _ := rfl
  Isolated R f := ∀ env r s₁ s₂, R env r s₁ s₂ → ToResponse.toRes (f s₁).2 = ToResponse.toRes (f s₂).2
  step_isolated _ _ hI env r s₁ s₂ _ h := hI env r s₁ s₂ h

/-- A pure answer. -/
instance (priority := low) [ToResponse ρ] : Handler σ ρ where
  effect := .pure
  pathArity := 0
  inputs := []
  step a _ _ s _ := (ToResponse.toRes a, s)
  errors _ _ _ _ := []
  step_safe _ _ _ _ _ _ := rfl
  Preserved _ _ := True
  step_preserved _ _ _ _ _ _ _ hs := hs
  ErrStable _ := True
  errors_stable _ _ _ _ _ _ _ _ := rfl
  Isolated _ _ := True
  step_isolated _ _ _ _ _ _ _ _ _ := rfl

/-! ## Endpoints -/

def Method.Safe (m : Method) : Prop := m = .get ∨ m = .head

theorem Method.eq_of_beq' {a b : Method} (h : (a == b) = true) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

structure Endpoint (σ : Type) where
  method : Method
  template : String
  step : Env → Req → σ → Res × σ
  effect : Effect
  pathArity : Nat
  inputs : List String
  bodyLimit : Nat := 1024 * 1024
  /-- The handler's elaborated type, recorded by `api!`. -/
  signature : String := ""
  /-- A GET or HEAD endpoint never changes the state. -/
  step_safe : method.Safe → ∀ env r s, (step env r s).2 = s
  /-- The obligation for preserving `I`, computed from the signature. -/
  Preserved : (σ → Prop) → Prop
  step_preserved : ∀ I, Preserved I → ∀ env r s, I s → I (step env r s).2
  /-- The isolation obligation under `R`, computed from the signature. -/
  Isolated : Rel σ → Prop
  step_isolated : ∀ R, Isolated R → ∀ env r s₁ s₂, R env r s₁ s₂ → (step env r s₁).1 = (step env r s₂).1

namespace Endpoint

/-- Build an endpoint. `hsafe`: a safe method's handler has a safe effect. -/
def make {σ : Type} {τ : Type u} (m : Method) (t : String) (h : τ) [H : Handler σ τ]
    (hsafe : m.Safe → H.effect.Safe) (limit : Nat := 1024 * 1024) : Endpoint σ where
  method := m
  template := t
  bodyLimit := limit
  step env r s := H.step h env r s 0
  effect := H.effect
  pathArity := H.pathArity
  inputs := H.inputs
  step_safe hm env r s := H.step_safe (hsafe hm) h env r s 0
  Preserved I := H.Preserved I h
  step_preserved I hp env r s hs := H.step_preserved I h hp env r s 0 hs
  Isolated R := H.Isolated R h
  step_isolated R hI env r s₁ s₂ hR := H.step_isolated R h hI env r s₁ s₂ 0 hR

/-- Fails with a readable message when a safe method's handler can change
    state. -/
macro "endpoint_safe" : tactic =>
  `(tactic| first
    | decide
    | fail "a GET or HEAD endpoint must not change state, but this handler's effect is `writes`. \
Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.")

theorem unsafe_post : ¬ Method.Safe .post := by intro h; rcases h with h | h <;> cases h
theorem unsafe_put : ¬ Method.Safe .put := by intro h; rcases h with h | h <;> cases h
theorem unsafe_patch : ¬ Method.Safe .patch := by intro h; rcases h with h | h <;> cases h
theorem unsafe_delete : ¬ Method.Safe .delete := by intro h; rcases h with h | h <;> cases h

/-- `GET`: the handler's effect must be safe (`pure` or `reads`), proved
    when the endpoint is built. -/
def get {σ : Type} {τ : Type u} (t : String) (h : τ) [H : Handler σ τ] (safe : H.effect.Safe := by endpoint_safe) :
    Endpoint σ :=
  make .get t h (fun _ => safe)

def head {σ : Type} {τ : Type u} (t : String) (h : τ) [H : Handler σ τ] (safe : H.effect.Safe := by endpoint_safe) :
    Endpoint σ :=
  make .head t h (fun _ => safe)

def post {σ : Type} {τ : Type u} (t : String) (h : τ) [Handler σ τ] (limit : Nat := 1024 * 1024) : Endpoint σ :=
  make .post t h (fun hm => absurd hm unsafe_post) limit
def put {σ : Type} {τ : Type u} (t : String) (h : τ) [Handler σ τ] (limit : Nat := 1024 * 1024) : Endpoint σ :=
  make .put t h (fun hm => absurd hm unsafe_put) limit
def patch {σ : Type} {τ : Type u} (t : String) (h : τ) [Handler σ τ] (limit : Nat := 1024 * 1024) : Endpoint σ :=
  make .patch t h (fun hm => absurd hm unsafe_patch) limit
def delete {σ : Type} {τ : Type u} (t : String) (h : τ) [Handler σ τ] (limit : Nat := 1024 * 1024) : Endpoint σ :=
  make .delete t h (fun hm => absurd hm unsafe_delete) limit

def withSignature (e : Endpoint σ) (s : String) : Endpoint σ := { e with signature := s }

/-- Run against a store: a fresh environment, and the whole request
    (authentication, decoding, the handler) in one atomic step. -/
def toRoute (e : Endpoint σ) (store : Store σ) : Route where
  method := e.method
  template := e.template
  handler req := do
    let env ← Env.fresh
    let req := { req with params := req.params ++ Retry.routeParams e.method e.template e.inputs }
    store.modify fun s => let (res, s') := e.step env req s; (s', res)
  bodyLimit := e.bodyLimit
  name := if e.signature.isEmpty then none else some e.signature

/-- One line: method, template, effect, inputs, and the signature. -/
def describe (e : Endpoint σ) : String :=
  s!"{e.method} {e.template} [{e.effect.label}; {", ".intercalate e.inputs}]" ++
    (if e.signature.isEmpty then "" else s!"\n    : {e.signature}")

end Endpoint

/-! ## APIs, and their meaning as a system -/

abbrev Api (σ : Type) := List (Endpoint σ)

namespace Api

def routes (api : Api σ) (store : Store σ) : List Route := api.map (·.toRoute store)

/-- Prefix every template (e.g. `"/api"`). -/
def under (pre : String) (api : Api σ) : Api σ :=
  let pre := if pre.endsWith "/" then (pre.dropEnd 1).toString else pre
  api.map fun e => { e with template := if e.template == "/" then pre else pre ++ e.template }

def service (api : Api σ) (store : Store σ) (stack : Stack := {}) : Service :=
  Service.ofRouter (Router.build! (api.routes store)) stack

def describe (api : Api σ) : String := "\n".intercalate (api.map Endpoint.describe)

/-- The routing table, as the router resolves it. -/
def entries (api : Api σ) : List (Endpoint σ × Method × List Seg) :=
  api.filterMap fun e => (parseTemplate e.template).toOption.map fun segs => (e, e.method, segs)

/-- The API's meaning: route with the same `resolveIn` the router uses, then
    run the endpoint, with its identity passed as the router passes it
    (`Retry.routeParams`). (Middleware is outside it.) -/
def step (api : Api σ) (env : Env) (r : Req) (s : σ) : Res × σ :=
  match Router.resolveIn api.entries .redirect r with
  | .respond res => (res, s)
  | .route e ps => e.step env { r with params := ps ++ Retry.routeParams e.method e.template e.inputs } s

/-- The API as a transition system, for the property library. -/
def toSys (api : Api σ) (init : σ → Prop) : Props.Sys where
  World := σ
  Req := Req
  Res := Res
  Env := Env
  step env r s := api.step env r s
  init := init

theorem mem_entries {api : Api σ} {x : Endpoint σ × Method × List Seg} (h : x ∈ api.entries) :
    x.1 ∈ api ∧ x.2.1 = x.1.method := by
  simp only [entries, List.mem_filterMap, Option.map_eq_some_iff] at h
  obtain ⟨e, he, segs, _, rfl⟩ := h
  exact ⟨he, rfl⟩

/-- What the router resolves to is an endpoint of the API whose method is
    the request's, or `GET` for a `HEAD` request. -/
theorem resolveIn_route {api : Api σ} {r : Req} {e : Endpoint σ} {ps}
    (h : Router.resolveIn api.entries .redirect r = .route e ps) :
    e ∈ api ∧ (e.method = r.method ∨ (r.method = .head ∧ e.method = .get)) := by
  unfold Router.resolveIn at h
  split at h
  · cases h
  split at h
  · split at h <;> cases h
  dsimp only at h
  split at h
  · cases h
  have hmem : ∀ x ∈ Router.candidatesIn api.entries r.path, x.1 ∈ api.entries := by
    intro x hx
    simp only [Router.candidatesIn, List.mem_mergeSort, List.mem_filterMap, Option.map_eq_some_iff] at hx
    obtain ⟨y, hy, _, _, rfl⟩ := hx
    exact hy
  split at h
  · rename_i x hfind
    cases h
    have hm := mem_entries (hmem _ (List.mem_of_find?_eq_some hfind))
    have hp := List.find?_some hfind
    exact ⟨hm.1, .inl (by rw [← hm.2]; exact Method.eq_of_beq' hp)⟩
  · split at h
    · rename_i _ _ _ _ _ hhead hfind'
      cases h
      have hm := mem_entries (hmem _ (List.mem_of_find?_eq_some hfind'))
      have hp := List.find?_some hfind'
      exact ⟨hm.1, .inr ⟨hhead, by rw [← hm.2]; exact Method.eq_of_beq' hp⟩⟩
    · cases h
    · cases h

/-- **GET and HEAD never change the state**, for every typed API: each such
    endpoint carries the proof, and unrouted requests change nothing. -/
theorem step_safe (api : Api σ) (env : Env) (r : Req) (s : σ) (hm : r.method.Safe) :
    (api.step env r s).2 = s := by
  unfold step
  split
  · rfl
  · rename_i e ps hr
    obtain ⟨_, hmeth⟩ := resolveIn_route hr
    apply e.step_safe
    rcases hmeth with h | ⟨_, h⟩
    · rw [h]; exact hm
    · rw [h]; exact .inl rfl

/-- **Invariants of a typed API.** If `I` holds initially and every
    endpoint's `Preserved I` obligation (computed from its signature) is
    discharged, `I` holds in every reachable state. -/
theorem inductive_of (api : Api σ) {init : σ → Prop} {I : σ → Prop} (hinit : ∀ s, init s → I s)
    (hp : ∀ e ∈ api, e.Preserved I) : Props.Inductive (api.toSys init) I := by
  refine ⟨hinit, fun env r s hs => ?_⟩
  show I (api.step env r s).2
  unfold step
  split
  · exact hs
  · rename_i e ps hr
    exact e.step_preserved I (hp _ (resolveIn_route hr).1) env _ s hs

/-- **Isolation for typed APIs.** For a request authenticated as `p`, the
    whole response depends only on what `p` may see (`ViewOf`), provided
    each endpoint discharges its `Isolated` obligation, computed from its
    signature. Routing does not read the state; every input is extracted
    the same way in both states; after `Auth`, the handler body only has to
    answer alike in states that look the same to the actor. -/
theorem noninterference [A : Authenticates σ α] [V : ViewOf σ α] (api : Api σ) (p : α)
    (hiso : ∀ e ∈ api, e.Isolated fun env r s₁ s₂ => V.same p s₁ s₂ ∧ A.authenticate s₁ env r = .ok p)
    (env : Env) (r : Req) {s₁ s₂ : σ} (hv : V.same p s₁ s₂) (ha : A.authenticate s₁ env r = .ok p) :
    (api.step env r s₁).1 = (api.step env r s₂).1 := by
  unfold step
  split
  · rfl
  · rename_i e ps hr
    exact e.step_isolated _ (hiso e (resolveIn_route hr).1) env _ s₁ s₂
      ⟨hv, by rw [A.authenticate_params]; exact ha⟩

end Api

/-! ## Compile-time checking: `api!` -/

open Elab Term Meta in
/-- The checks `api!` makes, for any endpoint kind: `toEp` projects an
    item to its `Endpoint`, `ctors` are the constructors with the index of
    the handler argument `h`, `tyIdx` the index of its type `τ`, and
    `withSig` records the signature. -/
def checkEndpoints (who : String) (items : Array Expr) (toEp : Expr → MetaM Expr)
    (ctors : List (Name × Nat)) (tyIdx : Nat) (withSig : Name) : TermElabM (Array Expr) := do
  let mut keys : List (Method × String) := []
  let mut out : Array Expr := #[]
  for it in items do
    let ep ← toEp it
    let m ← reduce (← mkAppM ``LeanApi.Endpoint.method #[ep])
    let t ← reduce (← mkAppM ``LeanApi.Endpoint.template #[ep])
    let n ← reduce (← mkAppM ``LeanApi.Endpoint.pathArity #[ep])
    if m.hasFVar || t.hasFVar || n.hasFVar || m.hasMVar || t.hasMVar || n.hasMVar then
      throwError "{who}: could not compute an endpoint's method, template and path arity statically"
    let mv ← unsafe evalExpr Method (mkConst ``LeanApi.Method) m
    let tv ← unsafe evalExpr String (mkConst ``String) t
    let nv ← unsafe evalExpr Nat (mkConst ``Nat) n
    let found := ctors.findSome? fun (c, i) =>
      (it.find? (·.isAppOf c)).bind fun app => (app.getAppArgs[tyIdx]?).bind fun τ =>
        (app.getAppArgs[i]?).map fun h => (τ, h)
    let (hName, sig) ← match found with
      | some (τ, h) =>
        let hName := match h.getAppFn.constName? with
          | some c => s!"`{c}`"
          | none => "the handler"
        pure (hName, toString (← ppExpr τ))
      | none => pure ("the handler", "")
    match parseTemplate tv with
    | .error msg => throwError "{who}: {mv} {tv}: {msg}"
    | .ok segs =>
      let k := (segs.filter fun | .lit _ => false | _ => true).length
      unless k == nv do
        throwError "{who}: {mv} {tv} has {k} path parameter(s), but {hName} takes {nv} `Path` argument(s):\n  {sig}"
    keys := keys ++ [(mv, tv)]
    out := out.push (← mkAppM withSig #[it, toExpr sig])
  let errs := routeErrors keys
  unless errs.isEmpty do
    throwError m!"{who}: invalid routes:\n  {"\n  ".intercalate errs}"
  return out

open Elab Term Meta in
/-- Elaborate a list literal and collect its items. -/
def listItems (who : String) (xs : Syntax) (expectedType : Expr) : TermElabM (Array Expr) := do
  let e ← instantiateMVars (← elabTerm xs (some expectedType))
  let mut items : Array Expr := #[]
  let mut l ← whnfR e
  repeat
    match l.getAppFnArgs with
    | (``List.cons, #[_, h, t]) => items := items.push h; l ← whnfR t
    | (``List.nil, _) => break
    | _ => throwError "{who}: expected a list literal"
  return items

open Elab Term Meta in
/-- `api! [e₁, e₂, …]` elaborates a list of endpoints and, for each one,
    checks that the template parses and has exactly as many parameters as
    the handler has `Path` arguments, records the handler's elaborated type
    as its signature, and rejects conflicting routes. The list is an
    `Api σ` (in-memory endpoints) or a `DbApi s` (LeanDB programs), by the
    expected type. -/
elab "api!" xs:term : term <= expectedType => do
  let expectedType ← instantiateMVars expectedType
  let elemTy := (← whnfR expectedType).appArg!
  if (← whnfR elemTy).isAppOf `LeanApi.DbEndpoint then
    let items ← listItems "api!" xs expectedType
    -- `{s} [IsSchema s] {τ} (t) (h)`: τ is argument 2, h is argument 4.
    let ctors := [`get, `head, `post, `put, `patch, `delete].map fun c =>
      (`LeanApi.DbEndpoint ++ c, 4)
    let out ← checkEndpoints "api!" items (fun it => mkAppM `LeanApi.DbEndpoint.toEndpoint #[it])
      ctors 2 `LeanApi.DbEndpoint.withSignature
    mkListLit elemTy out.toList
  else
    let items ← listItems "api!" xs expectedType
    -- Every constructor takes `{σ τ}` first; `h : τ` follows the template
    -- (and, for `make`, the method).
    let ctors := [(``LeanApi.Endpoint.make, 4), (``LeanApi.Endpoint.get, 3), (``LeanApi.Endpoint.head, 3),
      (``LeanApi.Endpoint.post, 3), (``LeanApi.Endpoint.put, 3), (``LeanApi.Endpoint.patch, 3),
      (``LeanApi.Endpoint.delete, 3)]
    let out ← checkEndpoints "api!" items pure ctors 1 ``LeanApi.Endpoint.withSignature
    mkListLit elemTy out.toList

end LeanApi
