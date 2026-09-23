/-
  Typed endpoints (docs/ENDPOINTS.md).

  An endpoint is a plain function whose type is its specification:

    def editNote (me : Auth User) (id : Path NoteId) (rev : IfMatch Rev) (edit : Body NoteEdit) :
        Writes State (Except EditError (Versioned NoteView))

  * Inputs are parameters; each parameter's type says where it comes from
    (`FromRequest σ α`, an open class; `Path` is positional).
  * The effect on state is `Reads σ` / `Writes σ` (pure functions run
    atomically against a `Store σ`), `IO` (explicit escape), or none.
  * Success shapes are `ToResponse α` (`Created`, `Versioned`, `Paged`,
    `NoContent`, JSON); failures are `Except ε` with `ToProblem ε`, whose
    status is typed as a 4xx/5xx.

  `Handler σ τ` computes, by instance resolution over the arrows of `τ`,
  the runner plus the endpoint's effect, path arity and input kinds.
  `Endpoint.get` requires a proof, by `decide`, that the effect is safe.
  `api!` checks path arity against templates and route conflicts at
  compile time, and records each endpoint's elaborated signature.
-/
import LeanApi.Http.Router
import LeanApi.Http.Extract
import LeanApi.Http.Middleware
import LeanApi.Auth.Basic
import LeanApi.Util.Base64
import LeanApi.Runtime.Server
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

/-! ## Effects -/

/-- Reads the state; cannot change it. -/
def Reads (σ α : Type) := σ → α

/-- Changes the state, atomically: the new state and the answer. -/
def Writes (σ α : Type) := σ → σ × α

/-- What an endpoint may do to state, computed from its type. -/
inductive Effect where
  | pure | reads | writes | io
  deriving DecidableEq, Repr, Inhabited

/-- Safe methods (`GET`, `HEAD`) may only have these effects. -/
def Effect.Safe : Effect → Prop
  | .pure | .reads => True
  | .writes | .io => False

instance : DecidablePred Effect.Safe := fun e => by cases e <;> unfold Effect.Safe <;> infer_instance

def Effect.label : Effect → String
  | .pure => "pure" | .reads => "reads" | .writes => "writes" | .io => "io"

/-! ## Typed statuses -/

/-- A success status: 2xx, by type. -/
abbrev SuccessStatus := {n : Nat // 200 ≤ n ∧ n < 300}

/-- An error status: 4xx or 5xx, by type. -/
abbrev ErrorStatus := {n : Nat // 400 ≤ n ∧ n < 600}

/-! ## Inputs -/

/-- The next `{…}` parameter of the route template, decoded as `α`. -/
structure Path (α : Type) where
  val : α

/-- A value decoded from the query string (`FromQuery α`). -/
structure Query (α : Type) where
  val : α

/-- The request body, decoded as `α`: JSON (`FromBody α`), and also a form
    when `FromForm α` exists. -/
structure Body (α : Type) where
  val : α

/-- A required header, decoded as `α`. -/
structure Header (name : String) (α : Type) where
  val : α

/-- The `If-Match` precondition, when sent: the quoted ETag, decoded as
    `α`. `*` and absence are `none` (no precondition). -/
structure IfMatch (α : Type) where
  val : Option α

/-- The authenticated actor, of the type the scheme produces. -/
structure Auth (α : Type) where
  val : α

/-- A fresh random token (24 bytes, base64url): randomness as an input. -/
structure FreshToken where
  val : String

instance : CoeHead (Path α) α := ⟨Path.val⟩
instance : CoeHead (Query α) α := ⟨Query.val⟩
instance : CoeHead (Body α) α := ⟨Body.val⟩
instance : CoeHead (Header n α) α := ⟨Header.val⟩
instance : CoeHead (Auth α) α := ⟨Auth.val⟩
instance : CoeHead FreshToken String := ⟨FreshToken.val⟩

/-- The context an input is extracted from. -/
structure Ctx (σ : Type) where
  store : Store σ
  req : Req

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

/-- How to obtain an input of type `α` from a request. Open: apps add their
    own instances. `kind` names the source, for `Api.describe`. -/
class FromRequest (σ : Type) (α : Type) where
  kind : String
  extract : Ctx σ → IO (Got α)

/-- A record from the query string. -/
class FromQuery (α : Type) where
  fromQuery : Extract α

/-- A record from a form body. -/
class FromForm (α : Type) where
  fromForm : List (String × String) → Decoded α

/-- How to obtain an actor of type `α`: any `Authenticator`, given the store. -/
class Authenticates (σ : Type) (α : Type) where
  authenticator : Store σ → Authenticator α

namespace Authenticates

/-- Session tokens looked up in the state: `Authorization: Bearer`, and the
    cookie `cookie` when given. -/
def sessions (lookup : σ → String → Option α) (cookie : Option String := none) (realm : String := "api") :
    Store σ → Authenticator α := fun st =>
  let verify (t : String) : IO (Option α) := st.read (lookup · t)
  match cookie with
  | some c => (bearer verify realm).orElse (sessionCookie c verify)
  | none => bearer verify realm

/-- Basic credentials checked against the state. -/
def passwords (verify : σ → String → String → Option α) (realm : String := "api") :
    Store σ → Authenticator α := fun st =>
  basic (fun u p => st.read (verify · u p)) realm

end Authenticates

instance [FromQuery α] : FromRequest σ (Query α) where
  kind := "query"
  extract c := pure ((Got.ofDecoded (FromQuery.fromQuery c.req)).map Query.mk)

instance [FromParam α] : FromRequest σ (Header n α) where
  kind := s!"header {n}"
  extract c := pure ((Got.ofDecoded (Extract.header (α := α) n c.req)).map Header.mk)

/-- Strip the quotes of an entity tag (`"3"`, `W/"3"`). -/
def unquoteETag (s : String) : String :=
  let s := s.trimAscii.toString
  let s := if s.startsWith "W/" then (s.drop 2).toString else s
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then ((s.drop 1).dropEnd 1).toString else s

instance [FromParam α] : FromRequest σ (IfMatch α) where
  kind := "if-match"
  extract c := pure <|
    match c.req.header? "if-match" with
    | none => .ok ⟨none⟩
    | some v =>
      if v.trimAscii.toString == "*" then .ok ⟨none⟩ else
      match FromParam.fromParam (α := α) (unquoteETag v) with
      | .ok a => .ok ⟨some a⟩
      | .error m => .invalid [⟨"header.if-match", m⟩]

instance [Authenticates σ α] : FromRequest σ (Auth α) where
  kind := "auth"
  extract c := do
    let a := Authenticates.authenticator (σ := σ) (α := α) c.store
    match ← a.run c.req with
    | .ok who => return .ok ⟨who⟩
    | .error .missing => return .reject (unauthorized a.challenge)
    | .error (.invalid _) => return .reject (unauthorized a.challenge "invalid credentials")

instance : FromRequest σ FreshToken where
  kind := "fresh token"
  extract _ := do return .ok ⟨Base64.encodeUrl (← IO.getRandomBytes 24)⟩

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
  extract c := pure <|
    match c.req.contentType? with
    | some ct =>
      if ct == jsonType then (classify (Extract.json (α := α) c.req)).map Body.mk
      else if ct == formType then
        (classify (do FromForm.fromForm (← Extract.formPairs c.req))).map Body.mk
      else .reject (unsupported [jsonType, formType])
    | none => .reject (unsupported [jsonType, formType])

/-- A JSON body. -/
instance [FromBody α] : FromRequest σ (Body α) where
  kind := "body (json)"
  extract c := pure <|
    match c.req.contentType? with
    | some ct => if ct == jsonType then (classify (Extract.json (α := α) c.req)).map Body.mk
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

def ToProblem.problem [ToProblem ε] (e : ε) : Problem :=
  Problem.make (ToProblem.status e).1 (ToProblem.detail e)

instance [ToResponse α] [ToProblem ε] : ToResponse (Except ε α) where
  toRes
    | .ok a => ToResponse.toRes a
    | .error e => (ToProblem.problem e).toRes

/-- The resource does not exist, or the caller may not know it does. -/
structure NotFound where
  deriving Repr, Inhabited

instance : ToProblem NotFound := ⟨fun _ => ⟨404, by decide⟩, fun _ => none⟩

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
    Instance resolution computes its effect, path arity and input kinds. -/
class Handler (σ : Type) (τ : Type) where
  effect : Effect
  pathArity : Nat
  inputs : List String
  /-- Run with the index of the next `Path` parameter. -/
  run : τ → Ctx σ → Nat → IO Res
  /-- The field errors of all inputs, without running the handler. -/
  errors : Ctx σ → Nat → IO (List FieldError)

/-- The `i`th path parameter, decoded. -/
def pathAt [FromParam α] (r : Req) (i : Nat) : Decoded α :=
  match r.params[i]? with
  | some (n, v) =>
    match FromParam.fromParam v with
    | .ok a => .ok a
    | .error m => .error [⟨s!"path.{n}", m⟩]
  | none => .error [⟨s!"path[{i}]", "missing path parameter"⟩]

instance [FromParam α] [H : Handler σ β] : Handler σ (Path α → β) where
  effect := H.effect
  pathArity := H.pathArity + 1
  inputs := "path" :: H.inputs
  run f c i :=
    match pathAt (α := α) c.req i with
    | .ok a => H.run (f ⟨a⟩) c (i + 1)
    | .error es => do return validationRes (es ++ (← H.errors c (i + 1)))
  errors c i := do
    let mine := match pathAt (α := α) c.req i with | .ok _ => [] | .error es => es
    return mine ++ (← H.errors c (i + 1))

instance (priority := low) [R : FromRequest σ α] [H : Handler σ β] : Handler σ (α → β) where
  effect := H.effect
  pathArity := H.pathArity
  inputs := R.kind :: H.inputs
  run f c i := do
    match ← R.extract c with
    | .ok a => H.run (f a) c i
    | .invalid es => return validationRes (es ++ (← H.errors c i))
    | .reject r => return r
  errors c i := do
    let mine ← match ← R.extract c with
      | .invalid es => pure es
      | _ => pure []
    return mine ++ (← H.errors c i)

instance [ToResponse ρ] : Handler σ (Reads σ ρ) where
  effect := .reads
  pathArity := 0
  inputs := []
  run f c _ := do return ToResponse.toRes (← c.store.read f)
  errors _ _ := pure []

instance [ToResponse ρ] : Handler σ (Writes σ ρ) where
  effect := .writes
  pathArity := 0
  inputs := []
  run f c _ := do return ToResponse.toRes (← c.store.modify f)
  errors _ _ := pure []

/-- The explicit escape hatch: arbitrary `IO`, visible in the signature. -/
instance [ToResponse ρ] : Handler σ (IO ρ) where
  effect := .io
  pathArity := 0
  inputs := []
  run act _ _ := do return ToResponse.toRes (← act)
  errors _ _ := pure []

/-- A pure answer. -/
instance (priority := low) [ToResponse ρ] : Handler σ ρ where
  effect := .pure
  pathArity := 0
  inputs := []
  run a _ _ := pure (ToResponse.toRes a)
  errors _ _ := pure []

/-! ## Endpoints and APIs -/

structure Endpoint (σ : Type) where
  method : Method
  template : String
  run : Ctx σ → IO Res
  effect : Effect
  pathArity : Nat
  inputs : List String
  bodyLimit : Nat := 1024 * 1024
  /-- The handler's elaborated type, recorded by `api!`. -/
  signature : String := ""

namespace Endpoint

def make {σ τ : Type} (m : Method) (t : String) (h : τ) [H : Handler σ τ] (limit : Nat := 1024 * 1024) :
    Endpoint σ where
  method := m
  template := t
  bodyLimit := limit
  run c := H.run h c 0
  effect := H.effect
  pathArity := H.pathArity
  inputs := H.inputs

/-- Fails with a readable message when a safe method's handler can change
    state. -/
macro "endpoint_safe" : tactic =>
  `(tactic| first
    | decide
    | fail "a GET or HEAD endpoint must not change state, but this handler's effect is `writes` or `io`. \
Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.")

/-- `GET`: the handler's effect must be safe (`pure` or `reads`), proved
    when the endpoint is built. -/
def get {σ τ : Type} (t : String) (h : τ) [H : Handler σ τ] (_safe : H.effect.Safe := by endpoint_safe) :
    Endpoint σ :=
  make .get t h

def head {σ τ : Type} (t : String) (h : τ) [H : Handler σ τ] (_safe : H.effect.Safe := by endpoint_safe) : Endpoint σ :=
  make .head t h

def post {σ τ : Type} (t : String) (h : τ) [Handler σ τ] (limit : Nat := 1024 * 1024) : Endpoint σ :=
  make .post t h limit
def put {σ τ : Type} (t : String) (h : τ) [Handler σ τ] (limit : Nat := 1024 * 1024) : Endpoint σ :=
  make .put t h limit
def patch {σ τ : Type} (t : String) (h : τ) [Handler σ τ] (limit : Nat := 1024 * 1024) : Endpoint σ :=
  make .patch t h limit
def delete {σ τ : Type} (t : String) (h : τ) [Handler σ τ] (limit : Nat := 1024 * 1024) : Endpoint σ :=
  make .delete t h limit


def withSignature (e : Endpoint σ) (s : String) : Endpoint σ := { e with signature := s }

def toRoute (e : Endpoint σ) (store : Store σ) : Route where
  method := e.method
  template := e.template
  handler req := e.run ⟨store, req⟩
  bodyLimit := e.bodyLimit
  name := if e.signature.isEmpty then none else some e.signature

/-- One line: method, template, effect, inputs, and the signature. -/
def describe (e : Endpoint σ) : String :=
  s!"{e.method} {e.template} [{e.effect.label}; {", ".intercalate e.inputs}]" ++
    (if e.signature.isEmpty then "" else s!"\n    : {e.signature}")

end Endpoint

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

end Api

/-! ## Compile-time checking: `api!` -/

open Elab Term Meta in
/-- `api! [e₁, e₂, …]` elaborates a list of endpoints and, for each one,
    checks that the template parses and has exactly as many parameters as
    the handler has `Path` arguments, records the handler's elaborated type
    as its signature, and rejects conflicting routes. -/
elab "api!" xs:term : term <= expectedType => do
  let e ← elabTerm xs (some expectedType)
  let e ← instantiateMVars e
  let mut items : Array Expr := #[]
  let mut l ← whnfR e
  repeat
    match l.getAppFnArgs with
    | (``List.cons, #[_, h, t]) => items := items.push h; l ← whnfR t
    | (``List.nil, _) => break
    | _ => throwError "api!: expected a list literal"
  let mut keys : List (Method × String) := []
  let mut out : Array Expr := #[]
  for it in items do
    let m ← reduce (← mkAppM ``LeanApi.Endpoint.method #[it])
    let t ← reduce (← mkAppM ``LeanApi.Endpoint.template #[it])
    let n ← reduce (← mkAppM ``LeanApi.Endpoint.pathArity #[it])
    if m.hasFVar || t.hasFVar || n.hasFVar || m.hasMVar || t.hasMVar || n.hasMVar then
      throwError "api!: could not compute an endpoint's method, template and path arity statically"
    let mv ← unsafe evalExpr Method (mkConst ``LeanApi.Method) m
    let tv ← unsafe evalExpr String (mkConst ``String) t
    let nv ← unsafe evalExpr Nat (mkConst ``Nat) n
    -- The handler: every constructor takes `{σ τ}` first; `h : τ` follows
    -- the template (and, for `make`, the method).
    let ctors := [(``LeanApi.Endpoint.make, 4), (``LeanApi.Endpoint.get, 3), (``LeanApi.Endpoint.head, 3),
      (``LeanApi.Endpoint.post, 3), (``LeanApi.Endpoint.put, 3), (``LeanApi.Endpoint.patch, 3),
      (``LeanApi.Endpoint.delete, 3)]
    let found := ctors.findSome? fun (c, i) =>
      (it.find? (·.isAppOf c)).bind fun app => (app.getAppArgs[1]?).bind fun τ =>
        (app.getAppArgs[i]?).map fun h => (τ, h)
    let (hName, sig) ← match found with
      | some (τ, h) =>
        let hName := match h.getAppFn.constName? with
          | some c => s!"`{c}`"
          | none => "the handler"
        pure (hName, toString (← ppExpr τ))
      | none => pure ("the handler", "")
    match parseTemplate tv with
    | .error msg => throwError "api!: {mv} {tv}: {msg}"
    | .ok segs =>
      let k := (segs.filter fun | .lit _ => false | _ => true).length
      unless k == nv do
        throwError "api!: {mv} {tv} has {k} path parameter(s), but {hName} takes {nv} `Path` argument(s):\n  {sig}"
    keys := keys ++ [(mv, tv)]
    out := out.push (← mkAppM ``LeanApi.Endpoint.withSignature #[it, toExpr sig])
  let errs := routeErrors keys
  unless errs.isEmpty do
    throwError m!"api!: invalid routes:\n  {"\n  ".intercalate errs}"
  let elemTy := (← whnfR (← instantiateMVars expectedType)).appArg!
  mkListLit elemTy out.toList

end LeanApi
