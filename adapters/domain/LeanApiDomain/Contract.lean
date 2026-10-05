import LeanApi.Http.DbEndpoint
import LeanContract.Http
import LeanContract.Generate
import LeanContract.Envelope

/-! Optional LeanContract bridge. Existing RFC 9457 endpoints are unaffected.
Only explicit, typed publications enter this adapter. Native lowering is trusted;
request codecs never receive actor, transaction scope, or the environment. -/
namespace LeanApi.Domain
open Lean LeanDb Ontology Contract

private def privateReply (r : Res) : Res :=
  r.setHeader "cache-control" "private, no-store"

/-- How a route's request body becomes the operation input. -/
inductive BodyFormat where
  /-- The Contract request envelope `{operation, kind, input}`, answered with Contract replies:
  the milestone 1 RPC routes of `operations := […]` apps. -/
  | envelope
  /-- The body is the input record itself, without its path-bound fields (GET has no body),
  answered with the `{"ok": v}` / `{"error": …}` envelope (decisions 5 and 15). -/
  | plain
  deriving Repr, BEq, DecidableEq

def frameworkReply (codecs : Contract.Http.Codecs) : CallError ε → Res
  | .domain _ => privateReply (Res.json (Contract.Http.protocolResponse "response.unexpected_domain_error") 500)
  | .unauthenticated => privateReply (Res.json (.mkObj [("tag", .str "unauthenticated")]) 401)
  | .forbidden => privateReply (Res.json (.mkObj [("tag", .str "forbidden")]) 403)
  | .decode errors => privateReply (Res.json (Contract.Http.decodeErrorResponse codecs errors) 400)
  | .incompatible mismatch => privateReply (Res.json
      (Contract.Http.incompatibleResponse codecs mismatch.expected mismatch.received) 409)
  | .protocol error => privateReply (Res.json (Contract.Http.protocolResponse error.code)
      (error.status.getD 400))
  | .transport _ => privateReply (Res.json (Contract.Http.protocolResponse "infrastructure.unavailable") 503)
  | .cancelled => privateReply (Res.json (Contract.Http.protocolResponse "request.cancelled") 409)

/-- The stable public code of a database fault: `database.busy` (locking, retryable),
`storage.corrupt` (a stored row or value that does not decode or fails its check, e.g. a
raw-SQL edit), else `database.unavailable`. The fault's message (table, column, SQL) is
never sent. -/
def faultCode : DbFault → String
  | .locking _ => "database.busy"
  | .corruption _ => "storage.corrupt"
  | _ => "database.unavailable"

/-- Infrastructure detail never enters a public envelope. Locking remains retryable. -/
def databaseReply (fault : DbFault) : Res :=
  let res := privateReply (Res.json (Contract.Http.protocolResponse (faultCode fault)) (faultStatus fault))
  if faultStatus fault == 503 then res.setHeader "retry-after" "1" else res

/-- The framework class of a failure (decision 5), with its precise code for the
`x-leanapp-error` header. The body never carries infrastructure detail. -/
def frameworkClass : CallError ε → Contract.Envelope.Framework × String
  | .domain _ => (.internal, "response.unexpected_domain_error")
  | .unauthenticated => (.unauthorized, "auth.unauthenticated")
  | .forbidden => (.forbidden, "auth.forbidden")
  | .decode _ => (.badRequest, "request.decode")
  | .incompatible _ => (.badRequest, "operation.incompatible")
  | .protocol error => (match error.status.getD 400 with
      | 400 | 413 | 422 => .badRequest
      | 401 => .unauthorized
      | 403 => .forbidden
      | 404 => .notFound
      | 409 => .conflict
      | 429 => .tooManyRequests
      | 501 | 503 => .unavailable
      | _ => .internal, error.code)
  | .transport _ => (.unavailable, "infrastructure.unavailable")
  | .cancelled => (.conflict, "request.cancelled")

/-- `{"error": "unauthorized"}` and friends, at the class's status. -/
def envelopeFailure (error : CallError ε) : Res :=
  let (framework, code) := frameworkClass error
  let reply := privateReply ((Res.json (Contract.Envelope.frameworkError framework) framework.status).setHeader
    "x-leanapp-error" code)
  if framework == .unavailable then reply.setHeader "retry-after" "1" else reply

/-- A framework failure in the route's reply format. -/
def failureReply (format : BodyFormat) (codecs : Contract.Http.Codecs) (error : CallError ε) : Res :=
  match format with
  | .envelope => frameworkReply codecs error
  | .plain => envelopeFailure error

def databaseReplyAt (format : BodyFormat) (fault : DbFault) : Res :=
  match format with
  | .envelope => databaseReply fault
  | .plain => envelopeFailure (.protocol ⟨faultCode fault,
      some (if faultStatus fault == 503 then 503 else 500), ""⟩ : CallError Empty)

/-- Status policy and codecs are paired with their operation before erasure. -/
def resultReplyAt (format : BodyFormat) (codecs : Contract.Http.Codecs) (operation : Operation kind Input Output Error)
    (status : Error → Nat) : CallResult Output Error → Res
  | .ok output => match format with
    | .envelope => privateReply (Res.json
        (Contract.Http.successResponse codecs operation.identity (operation.outputCodec.encode output)))
    | .plain => privateReply (Res.json (Contract.Envelope.ok operation.outputCodec output))
  | .error (.domain error) =>
    let code := status error
    if code < 400 || code > 599 then
      failureReply format codecs (.protocol ⟨"response.invalid_domain_status", some 500, ""⟩ : CallError Empty)
    else match format with
      | .envelope => privateReply (Res.json
          (Contract.Http.domainResponse codecs operation.identity (operation.errorCodec.encode error)) code)
      | .plain => privateReply (Res.json (Contract.Envelope.domainError operation.errorCodec error) code)
  | .error error => failureReply format codecs error

def resultReply (codecs : Contract.Http.Codecs) (operation : Operation kind Input Output Error)
    (status : Error → Nat) : CallResult Output Error → Res :=
  resultReplyAt .envelope codecs operation status

/-! ## Route bindings

An operation is published at an explicit `(method, path template, operation)` entry. A
`:name` segment binds the input field `name`; the remaining fields come from the body. -/


/-- One `:name` path segment bound to the input field `name`, through that field's
typed path codec and its canonical Wire encoding. -/
structure PathField where
  name : String
  decode : String → Validation Json

structure RouteBinding where
  method : LeanApi.Method := .post
  /-- A template such as `/books/:book/loans`. Literal segments match exactly. -/
  path : String
  /-- Exactly the template's `:name` segments, in order. -/
  fields : List PathField := []
  format : BodyFormat := .plain
  maxBodyBytes : Option Nat := some 16384

inductive TemplateSegment where
  | literal (text : String)
  | param (name : String)
  deriving Repr, BEq

private def literalChar (c : Char) : Bool :=
  c.toNat < 128 && (c.isAlphanum || c == '-' || c == '_' || c == '.')

private def paramName (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest => first.toNat < 128 && (first.isAlpha || first == '_') &&
      rest.all (fun c => c.toNat < 128 && (c.isAlphanum || c == '_'))

/-- Canonical templates only: no empty, `.` or `..` segment, no duplicate parameter. -/
def parseRouteTemplate (path : String) : Except String (List TemplateSegment) := do
  unless path.startsWith "/" do throw s!"route template must start with '/': {path}"
  if path == "/" then return []
  let raw := (path.drop 1).toString.splitOn "/"
  let mut segments := #[]
  for segment in raw do
    if segment.isEmpty then throw s!"empty segment in route template: {path}"
    if segment.startsWith ":" then
      let name := (segment.drop 1).toString
      unless paramName name do throw s!"invalid path parameter name '{segment}' in {path}"
      segments := segments.push (TemplateSegment.param name)
    else
      if segment == "." || segment == ".." || !segment.toList.all literalChar then
        throw s!"invalid literal segment '{segment}' in route template: {path}"
      segments := segments.push (TemplateSegment.literal segment)
  let names := segments.toList.filterMap fun | .param name => some name | _ => none
  if names.eraseDups.length != names.length then throw s!"duplicate path parameter in {path}"
  return segments.toList

def routeTemplateParams (path : String) : List String :=
  match parseRouteTemplate path with
  | .ok segments => segments.filterMap fun | .param name => some name | _ => none
  | .error _ => []

namespace RouteBinding

/-- The literal POST envelope binding of the milestone 1 RPC paths and the generated client. -/
def rpc (http : LeanApp.HttpBinding) : RouteBinding :=
  { method := .post, path := http.path, fields := [], format := .envelope, maxBodyBytes := http.maxBodyBytes }

def params (binding : RouteBinding) : List String := routeTemplateParams binding.path

/-- The core router spells parameters `{name}`. -/
def routerTemplate (binding : RouteBinding) : String :=
  match parseRouteTemplate binding.path with
  | .ok [] => "/"
  | .ok segments => String.join (segments.map fun
      | .literal text => "/" ++ text
      | .param name => "/{" ++ name ++ "}")
  | .error _ => binding.path

/-- What the portable binding and the generated client can express today: a literal POST
path carrying the request envelope. -/
def portable? (binding : RouteBinding) : Option LeanApp.HttpBinding :=
  if binding.method == .post && binding.format == .envelope && binding.fields.isEmpty &&
      binding.params.isEmpty then
    some { path := binding.path, maxBodyBytes := binding.maxBodyBytes }
  else none

def methodName (binding : RouteBinding) : String := toString binding.method

/-- Manifest form. A portable binding keeps the exact milestone 1 bytes. -/
def toJson (binding : RouteBinding) : Json :=
  match binding.portable? with
  | some http => http.toJson
  | none => .mkObj [("path", .str binding.path), ("method", .str binding.methodName),
      ("maxBodyBytes", match binding.maxBodyBytes with | some cap => Lean.toJson cap | none => .null),
      ("params", .arr (binding.params.map Json.str).toArray),
      ("body", .str (match binding.format with | .envelope => "envelope" | .plain => "plain"))]

private def recordFields : WireSchema → Option (List String)
  | .named _ _ body => recordFields body
  | .record fields => some (fields.map Prod.fst)
  | _ => none

/-- Runtime validation, repeated by `Application.create` for bindings that did not come
from the checked `route_binding%` elaborator. -/
def validate (binding : RouteBinding) (writes : Bool) (input : WireSchema) : Validation Unit := do
  let segments ← match parseRouteTemplate binding.path with
    | .ok segments => pure segments
    | .error _ => Validation.fail "http.invalid_route_template" [] [("path", binding.path)]
  let params := segments.filterMap fun | .param name => some name | _ => none
  if binding.fields.map (·.name) != params then
    Validation.fail "http.path_fields_mismatch" [] [("path", binding.path)]
  let fields := (recordFields input).getD []
  for name in params do
    unless fields.contains name do
      Validation.fail "http.path_parameter_unbound" [] [("path", binding.path), ("parameter", name)]
  match binding.method with
  | .post => pure ()
  | .get =>
    if writes then Validation.fail "http.get_requires_query" [] [("path", binding.path)]
    if binding.format != .plain || fields.any (!params.contains ·) then
      Validation.fail "http.get_reads_path_only" [] [("path", binding.path)]
  | _ => Validation.fail "http.unsupported_method" [] [("path", binding.path)]
  if let some limit := binding.maxBodyBytes then
    if limit == 0 || limit > 2^32 then Validation.fail "http.invalid_body_limit" [] [("path", binding.path)]

end RouteBinding

private def badRequest (format : BodyFormat) (codecs : Contract.Http.Codecs) (code : String) : Res :=
  failureReply format codecs (.protocol ⟨code, some 400, ""⟩ : CallError Empty)

private def bodyJson (format : BodyFormat) (codecs : Contract.Http.Codecs) (req : Req) : Except Res Json :=
  match String.fromUTF8? req.body with
  | none => .error (badRequest format codecs "request.invalid_utf8")
  | some text => match Json.parse text with
    | .error _ => .error (badRequest format codecs "request.invalid_json")
    | .ok value => .ok value

private def isRecord : WireSchema → Bool
  | .named _ _ body => isRecord body
  | .record _ => true
  | _ => false

/-- The request envelope, checked against this exact operation identity and kind. -/
private def envelopeInput (codecs : Contract.Http.Codecs)
    (operation : Operation kind Input Output Error) (req : Req) : Except Res Json := do
  let value ← bodyJson .envelope codecs req
  let request ← (Contract.Http.decodeRequest codecs value).mapError
    (fun errors => frameworkReply codecs (.decode errors : CallError Empty))
  if request.operation != operation.identity then
    throw (frameworkReply codecs (.incompatible ⟨operation.identity, request.operation⟩ : CallError Empty))
  if request.kind != kind then
    throw (badRequest .envelope codecs "operation.kind_mismatch")
  return request.input

/-- The input record itself. An empty body is the empty record (or unit). -/
private def plainInput (codecs : Contract.Http.Codecs) (method : LeanApi.Method)
    (operation : Operation kind Input Output Error) (req : Req) : Except Res Json := do
  if req.body.isEmpty then
    return if isRecord operation.inputCodec.schema then Json.mkObj [] else Json.null
  if method == .get then throw (badRequest .plain codecs "request.unexpected_body")
  bodyJson .plain codecs req

/-- Path segments bind input fields by name. A body that also supplies a path field is
refused instead of silently preferring either value. -/
private def bindPath (codecs : Contract.Http.Codecs) (binding : RouteBinding) (req : Req)
    (input : Json) : Except Res Json := do
  if binding.fields.isEmpty then return input
  let .obj _ := input | throw (badRequest binding.format codecs "request.expected_object")
  let mut value := input
  for field in binding.fields do
    let some segment := req.param? field.name | throw (badRequest binding.format codecs "request.missing_path_parameter")
    if (value.getObjVal? field.name).toOption.isSome then throw (badRequest binding.format codecs "request.path_field_in_body")
    let encoded ← (Validation.prependPath [.key field.name] (field.decode segment)).mapError
      (fun errors => failureReply binding.format codecs (.decode errors : CallError Empty))
    value := value.setObjVal! field.name encoded
  return value

private def inputFromRequest (codecs : Contract.Http.Codecs) (binding : RouteBinding)
    (operation : Operation kind Input Output Error) (req : Req) : Except Res Input := do
  let raw ← match binding.format with
    | .envelope => envelopeInput codecs operation req
    | .plain => plainInput codecs binding.method operation req
  let value ← bindPath codecs binding req raw
  operation.inputCodec.decode value |>.mapError
    (fun errors => failureReply binding.format codecs (.decode errors : CallError Empty))

/-- A checked publication. The constructor is private: raw handlers need the explicit
`TrustedAdapter` entry point. Importing a storage entity does not export any route. -/
structure Published (s : Type) [IsSchema s] where
  private mk ::
  publicInfo : LeanApp.PublicOperation
  errorStatus : Contract.Http.ErrorStatus
  effect : Effect
  /-- The one HTTP entry that reaches this operation. -/
  route : RouteBinding
  /-- Preparation in continuation form: Read/Txn live in Type 1 and cannot be
  returned inside Type-0 IO. The continuation admits the prepared native program. -/
  runWith : Req → ((Env → DbProg s effect) → IO (Except DbFault Res)) → IO (Except DbFault Res)

/-- Native response metadata, excluded from public operation codecs. Applied only
after the transaction commits; aborted authentication must never issue cookies. -/
structure ReplyEdits where
  headers : List (String × String) := []
  cookies : List Res.Cookie := []
  /-- Replaces the encoded success value (the explicit token reply); `none` keeps it. -/
  value : Option (Json → Json) := none

def ReplyEdits.apply (edits : ReplyEdits) (reply : Res) : Res :=
  if edits.cookies.any (fun cookie => !cookie.valid) then
    privateReply (Res.json (Contract.Http.protocolResponse "response.invalid_cookie") 500)
  else
    privateReply <| edits.cookies.foldl Res.setCookie
      (edits.headers.foldl (fun reply (name, value) => reply.addHeader name value) reply)

/-- The portable description of a binding. A template or GET binding keeps its own
manifest form (`RouteBinding.toJson`); this record carries the path text. -/
def RouteBinding.publicHttp (binding : RouteBinding) : LeanApp.HttpBinding :=
  (binding.portable?).getD { path := binding.path, maxBodyBytes := binding.maxBodyBytes }

namespace TrustedAdapter
variable {s : Type} [IsSchema s]

/-- Trusted native query lowering at an explicit route. Reads cannot write. -/
def queryAt (codecs : Contract.Http.Codecs) (operation : Operation .query Input Output Error)
    (handler : Env → Req → Input → Read s (CallResult Output Error))
    (status : Error → Nat) (binding : RouteBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  ⟨⟨operation.describe, binding.publicHttp, metadata⟩, Contract.Http.ErrorStatus.ofOperation operation status, .reads,
    binding, fun req run => run fun env => match inputFromRequest codecs binding operation req with
      | .error response => pure response
      | .ok input => resultReplyAt binding.format codecs operation status <$> handler env req input⟩

/-- Trusted native query lowering. Reads cannot construct a transaction or write. -/
def query (codecs : Contract.Http.Codecs) (operation : Operation .query Input Output Error)
    (handler : Env → Req → Input → Read s (CallResult Output Error))
    (status : Error → Nat) (http : LeanApp.HttpBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  queryAt codecs operation handler status (RouteBinding.rpc http) metadata

/-- Trusted rank-2 command lowering at an explicit route. Any typed failure aborts every
write. Actor/profile resolution belongs in this program, after the environment is sampled. -/
def commandAt (codecs : Contract.Http.Codecs) (operation : Operation .command Input Output Error)
    (handler : Env → Req → Input → {σ : Type} → Txn σ s (CallError Error) Output)
    (status : Error → Nat) (binding : RouteBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  ⟨⟨operation.describe, binding.publicHttp, metadata⟩, Contract.Http.ErrorStatus.ofOperation operation status, .writes,
    binding, fun req run => run fun env => match inputFromRequest codecs binding operation req with
      | .error response => .pure response
      | .ok input => .bind
          (Txn.mapErr (fun error => resultReplyAt binding.format codecs operation status (.error error)) (handler env req input))
          (fun output => .pure (resultReplyAt binding.format codecs operation status (.ok output)))⟩

/-- Trusted rank-2 command lowering. Any typed failure aborts every write. Actor/profile
resolution belongs in this program, after the transaction's environment is sampled. -/
def command (codecs : Contract.Http.Codecs) (operation : Operation .command Input Output Error)
    (handler : Env → Req → Input → {σ : Type} → Txn σ s (CallError Error) Output)
    (status : Error → Nat) (http : LeanApp.HttpBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  commandAt codecs operation handler status (RouteBinding.rpc http) metadata

end TrustedAdapter

namespace TrustedAdapter
variable {s : Type} [IsSchema s]

/-- Expensive native preparation is outside the writer. Typed input decoding precedes
it; environment sampling/live actor resolution/final uniqueness stay in the Txn.
Session metadata leaves only after commit, and never through an Output codec. -/
def preparedCommandAt (codecs : Contract.Http.Codecs)
    (operation : Operation .command Input Output Error)
    (prepare : Req → Input → IO (CallResult Prepared Error))
    (handler : Env → Req → Input → Prepared →
      {Scope : Type} → Txn Scope s (CallError Error) (Output × ReplyEdits))
    (status : Error → Nat) (binding : RouteBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  { publicInfo := ⟨operation.describe, binding.publicHttp, metadata⟩,
    errorStatus := Contract.Http.ErrorStatus.ofOperation operation status,
    effect := .writes,
    route := binding,
    runWith := fun req run => do
      match inputFromRequest codecs binding operation req with
      | .error response => return .ok response
      | .ok input =>
        match ← prepare req input with
        | .error error => return .ok (resultReplyAt binding.format codecs operation status (.error error))
        | .ok prepared => run (fun env {Scope : Type} => Txn.bind
            (Txn.mapErr (fun error => resultReplyAt binding.format codecs operation status (.error error))
              (handler env req input prepared (Scope := Scope)))
            (fun (output, edits) =>
              if edits.cookies.any (fun cookie => !cookie.valid) then
                .throw (failureReply binding.format codecs (.protocol ⟨"response.invalid_cookie", some 500, ""⟩ : CallError Empty))
              else
                let reply := match edits.value, binding.format with
                  | none, _ => resultReplyAt binding.format codecs operation status (.ok output)
                  | some edit, .envelope => privateReply (Res.json (Contract.Http.successResponse codecs
                      operation.identity (edit (operation.outputCodec.encode output))))
                  | some edit, .plain => privateReply (Res.json
                      (.mkObj [("ok", edit (operation.outputCodec.encode output))]))
                .pure (edits.apply reply))) }

def preparedCommand (codecs : Contract.Http.Codecs)
    (operation : Operation .command Input Output Error)
    (prepare : Req → Input → IO (CallResult Prepared Error))
    (handler : Env → Req → Input → Prepared →
      {Scope : Type} → Txn Scope s (CallError Error) (Output × ReplyEdits))
    (status : Error → Nat) (http : LeanApp.HttpBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  preparedCommandAt codecs operation prepare handler status (RouteBinding.rpc http) metadata

end TrustedAdapter

namespace Published
variable {s : Type} [IsSchema s]

/-- Native runner injection keeps release-compatible core execution separate from
the newer DB-owned prepared runner used by an integrated source graph. -/
abbrev Executor (s : Type) [IsSchema s] :=
  DbProg.EnvExecutor s

def toRoute (publication : Published s) (dc : DbConns) (fresh : IO Env := Env.fresh)
    (execute : Executor s := DbProg.execWithEnv) : LeanApi.Route where
  method := publication.route.method
  template := publication.route.routerTemplate
  bodyLimit := publication.route.maxBodyBytes.getD (1024 * 1024)
  name := some s!"{publication.publicInfo.operation.identity.namespaceName}.{publication.publicInfo.operation.identity.name}"
  handler req := do
    match ← publication.runWith req (fun program => execute dc fresh program) with
    | .ok response => return response
    | .error fault => return databaseReplyAt publication.route.format fault

end Published

/-- Validated exact allowlist, shared by HTTP, native clients, and Contract.Generate. -/
structure Application (s : Type) [IsSchema s] where
  private mk ::
  publications : List (Published s)

namespace Application
variable {s : Type} [IsSchema s]

/-- Exactly the listed publications are routable. Each binding is validated against its
operation's input schema and effect; no two entries may share an identity or a route. -/
def create (publications : List (Published s)) : Validation (Application s) :=
  go publications [] [(.get, "/api/manifest")]
where
  go : List (Published s) → List OperationId → List (LeanApi.Method × String) → Validation (Application s)
    | [], _, _ => .ok ⟨publications⟩
    | publication :: rest, identities, routes =>
      let info := publication.publicInfo
      let http := match publication.route.portable? with
        | some http => http.validate
        | none => publication.route.validate (publication.effect == Effect.writes) info.operation.input
      match http, info.operation.identity.validate with
      | .error errors, _ | _, .error errors => .error errors
      | .ok _, .ok _ =>
        let route := (publication.route.method, publication.route.routerTemplate)
        if identities.contains info.operation.identity then Validation.fail "operation.duplicate_identity"
        else if !(LeanApi.routeErrors (route :: routes)).isEmpty then Validation.fail "http.duplicate_path"
        else if info.http.rateLimit.isSome then Validation.fail "http.unsupported_rate_limit"
        else go rest (info.operation.identity :: identities) (route :: routes)

def manifest (app : Application s) : List LeanApp.PublicOperation := app.publications.map (·.publicInfo)

def bindings (app : Application s) : List RouteBinding := app.publications.map (·.route)

/-- The served manifest. A route the portable binding cannot express (a template, GET, a
plain body) keeps its method, template and path parameters; portable routes keep the
exact milestone 1 bytes of `PublicOperation.manifest`. -/
def manifestJson (app : Application s) : Json :=
  .mkObj [("operations", .arr (app.publications.map fun publication =>
    publication.publicInfo.toJson.setObjVal! "http" publication.route.toJson).toArray)]

def routes (app : Application s) (dc : DbConns) (fresh : IO Env := Env.fresh)
    (execute : Published.Executor s := DbProg.execWithEnv) : List LeanApi.Route :=
  { method := .get, template := "/api/manifest", handler := fun _ =>
      pure (privateReply (Res.json app.manifestJson)) } ::
  app.publications.map (fun p => p.toRoute dc fresh execute)

def service (app : Application s) (dc : DbConns) (stack : Stack := {})
    (fresh : IO Env := Env.fresh) (execute : Published.Executor s := DbProg.execWithEnv) : Service :=
  { Service.ofRouter (Router.build! (app.routes dc fresh execute)) stack with
    bodyTooLarge := fun _ _ => privateReply
      (Res.json (Contract.Http.protocolResponse "request.body_too_large") 413)
    errorResponse := fun _ => privateReply
      (Res.json (Contract.Http.protocolResponse "infrastructure.unavailable") 500)
    logErrors := false }

/-- The generated browser client speaks the literal POST envelope only. Refuse to emit a
client whose manifest would disagree with the served routes. -/
def emitClient (app : Application s) (codecs : Contract.Http.Codecs) (out : System.FilePath)
    (runtime : String := "../../engine/LeanContract") : IO Unit := do
  if let some route := app.bindings.find? (·.portable?.isNone) then
    throw (IO.userError s!"generated client: {route.methodName} {route.path} needs a client that \
      supports path templates, GET and plain bodies")
  Contract.Generate.emitClient app.manifest codecs (app.publications.map (·.errorStatus)) out runtime

end Application
end LeanApi.Domain
