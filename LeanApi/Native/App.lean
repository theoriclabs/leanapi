import LeanApi.Core
import LeanApi.Native.Runtime
import LeanApi.Native.Routes
import LeanApi.Native.Principal
import LeanApi.Native.AuthDeriving
import LeanDb.Typed.Gate
import LeanContract.Generate

/-! # The native app: `app%`

```lean
-- An API with accounts: the credential is the domain's `credential C.profile C.hash`.
app% server where
  authentication := Member with Login
  api := api
  migrations := [addShelf := Book.addField shelf (fill := .general)]

-- An API with no accounts.
app% counters where
  api := api

def main (args : List String) : IO UInt32 := server.main args
```

`app%` derives the native schema (`native_schema%`, from the domain entities of the api's
namespace, plus the session table of an app with accounts), the migrations it lists, and one
constant: `Name : NativeApp …` (accounts) or `Name : PublicApp …` (no accounts). `Name.main`
runs LeanDB's migration gate and serves the api's routes.

Pages are LeanReact's: a `NativeApp`/`PublicApp` carries `pages`, extra GET routes served next to
the api, negotiated with a GET endpoint on the same path (`Accept: text/html` gets the page). -/

namespace LeanApi.Native
open LeanApi LeanDb LeanDb.Model LeanApi.Core

structure AppConfig where
  database : System.FilePath := "app.sqlite"
  port : UInt16 := 8080
  origin : Option String := none
  development : Bool := true
  clockFile : Option System.FilePath := none

/-- A GET route served next to the api (a page, an asset). When a GET endpoint has the same
path shape, a navigation (`Accept: text/html`) gets this route and any other client the
endpoint. -/
structure PageRoute where
  /-- A `:name` template, as in an `Api` (`/books/:book`). -/
  path : String
  handler : Req → IO Res

/-- An app with accounts: the api's routes over schema `s`, its session storage over profile
entity `Profile`, and its migrations. -/
structure NativeApp (s Profile : Type) [IsSchema s] [LeanDb.Model.Entity Profile] : Type 1 where
  profile : LeanDb.Native.EntityStorage s Profile
  store : Auth.Storage s Profile profile
  build : Context s Profile → Contract.Http.Codecs → Ontology.Validation (Application s)
  /-- The published operations with their routes, in api order. -/
  descriptions : List (LeanApi.Publication.PublicOperation × Contract.Http.ErrorStatus × RouteBinding)
  /-- The operations whose flow starts a session (`Auth.startSession`): a browser that calls
  one is signed in by its reply. -/
  authOperations : List Contract.OperationId := []
  /-- Declared schema migrations (`migration%`), handed to LeanDB's startup gate. -/
  migrations : List LeanDb.SchemaMigration := []
  /-- Extra GET routes (LeanReact's pages and assets); see `PageRoute`. -/
  pages : Context s Profile → List PageRoute := fun _ => []

def describeAt (binding : RouteBinding) (operation : LeanApi.Core.Operation k Actor I O E) :
    LeanApi.Publication.PublicOperation × Contract.Http.ErrorStatus × RouteBinding :=
  ({ operation := operation.contract.describe, http := binding.publicHttp, metadata := {} },
    Contract.Http.ErrorStatus.ofOperation operation.contract (fun _ => 422), binding)

private def contractCodecs : IO Contract.Http.Codecs :=
  match Contract.Http.codecs with
  | .ok codecs => pure codecs
  | .error _ => throw (IO.userError "contract codec assembly failed")

/-- The generated client for the api's routes (templates, GET, plain bodies): each route as a
`ClientRoute`, with the served manifest embedded verbatim. -/
def emitRouteClient (descriptions : List (LeanApi.Publication.PublicOperation × Contract.Http.ErrorStatus × RouteBinding))
    (out : System.FilePath) : IO Unit := do
  let codecs ← contractCodecs
  let routes := descriptions.map fun (operation, _, route) =>
    ({ identity := operation.operation.identity, method := route.methodName, path := route.path,
       params := route.params, body := match route.format with | .plain => "plain" | .envelope => "envelope" } :
      Contract.Generate.ClientRoute)
  let manifest : Lean.Json := .mkObj [("operations", .arr (descriptions.map fun (operation, _, route) =>
    operation.toJson.setObjVal! "http" route.toJson).toArray)]
  Contract.Generate.emitClient (descriptions.map (·.1)) codecs (descriptions.map (·.2.1)) out "./runtime"
    (routes := routes) (manifestOverride := some manifest)

def NativeApp.emitClient {s Profile} [IsSchema s] [LeanDb.Model.Entity Profile]
    (app : NativeApp s Profile) (out : System.FilePath) : IO Unit :=
  emitRouteClient app.descriptions out

/-- The request clock: the system clock, or (tests) the seconds in a file. -/
def clock (path : Option System.FilePath) : IO Env := do
  match path with
  | none => Env.fresh
  | some path =>
    let text ← IO.FS.readFile path
    let some now := text.trimAscii.toString.toNat? | throw (IO.userError "invalid injected clock")
    pure { now }

private def cli (config : AppConfig) : List String → IO AppConfig
  | [] => pure config
  | "--database" :: value :: rest => cli {config with database := value} rest
  | "--clock-file" :: value :: rest => cli {config with clockFile := some value} rest
  | "--port" :: value :: rest => do
    let some port := value.toNat? | throw (IO.userError "invalid port")
    if port == 0 || port > 65535 then throw (IO.userError "invalid port")
    cli {config with port := UInt16.ofNat port} rest
  | _ => throw (IO.userError "unsupported app arguments")

/-- `LEANAPP_*` development overrides, applied over the authored configuration. -/
def configure (config : AppConfig) : IO AppConfig := do
  let mut args := []
  for (key, option) in [("LEANAPP_DATABASE", "--database"), ("LEANAPP_CLOCK_FILE", "--clock-file"),
      ("LEANAPP_PORT", "--port")] do
    if let some value ← IO.getEnv key then args := args ++ [option, value]
  cli config args

/-- A navigation request: the client lists `text/html` in Accept. `fetch` defaults to
`*/*`, and curl to `*/*`, so both reach the endpoint. -/
def acceptsHtml (req : Req) : Bool :=
  (req.headerAll "accept").any fun line => (line.splitOn ",").any fun range =>
    ((range.splitOn ";").headD "").trimAscii.toString.toLower == "text/html"

/-- Apps with plain routes answer framework failures, unknown paths included, in the
`{"error": …}` envelope. -/
def Application.bodyFormat {s} [IsSchema s] (publication : Application s) : BodyFormat :=
  if publication.bindings.any (·.format == .plain) then .plain else .envelope

/-- The served routes, with framework failures (an unknown path, a body too large, an
infrastructure fault) answered in `format`. -/
def routerService (routes : List Route) (format : BodyFormat) (codecs : Contract.Http.Codecs) : Service :=
  let router := Router.build! routes
  let router := if format == .plain then
      { router with notFound := fun _ => pure (envelopeFailure (Native.fault (Error := Empty) "route.not_found" 404)) }
    else router
  { Service.ofRouter router with
    bodyTooLarge := fun _ _ => failureReply format codecs (Native.fault (Error := Empty) "request.body_too_large" 413)
    errorResponse := fun _ => failureReply format codecs (Native.fault (Error := Empty) "infrastructure.unavailable")
    logErrors := false }

/-- The api's routes and the page routes, a page negotiated with a GET endpoint on the same
path shape. -/
def withPages (api : List Route) (pages : List PageRoute) : List Route :=
  let shape := fun (template : String) => (parseTemplate template).toOption.map (·.map Seg.shape)
  let template := fun (page : PageRoute) => ({ path := page.path : RouteBinding }).routerTemplate
  let pageRoutes := pages.map fun page =>
    match api.find? (fun r => r.method == .get && shape r.template == shape (template page)) with
    | some endpoint =>
      let negotiated : App := fun req => if acceptsHtml req then page.handler req else endpoint.handler req
      { endpoint with handler := negotiated }
    | none => Route.get (template page) page.handler
  let api := api.filter fun r => !(r.method == .get && pages.any (fun page => shape (template page) == shape r.template))
  api ++ pageRoutes

def NativeApp.service {s Profile} [IsSchema s] [LeanDb.Model.Entity Profile]
    (app : NativeApp s Profile) (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (publication : Application s) : Service :=
  let api := publication.routes context.dc context.fresh executePrepared
  routerService (withPages api (app.pages context)) publication.bodyFormat codecs

/-- Open the database and auth context, build the exact publication and run `k` with the
service. `serve` listens with it; tests drive it through the in-process HTTP transport. -/
def NativeApp.withService {s Profile} [IsSchema s] [LeanDb.Model.Entity Profile]
    (app : NativeApp s Profile) (config : AppConfig)
    (k : Context s Profile → Service → IO α) : IO α := do
    let cookies ← match Auth.CookieConfig.create
        (config.origin.getD s!"http://127.0.0.1:{config.port.toNat}") config.development with
      | .ok config => pure config
      | .error _ => throw (IO.userError "invalid app cookie origin")
    let codecs ← contractCodecs
    let dummyHash ← hashPassword (← Tokens.generate)
    let dc ← DbConns.open config.database (IsSchema.specs s) 2
    try
      let context : Context s Profile := {
        profile := app.profile
        store := app.store
        dc := dc
        cookies := cookies
        fresh := clock config.clockFile
        dummyHash := dummyHash
        kdf := { active := ← Std.Mutex.new 0, runs := some (← Std.Mutex.new 0) } }
      match app.build context codecs with
      | .error errors =>
        throw (IO.userError s!"app publication assembly failed: {errors.toList.map fun error => (error.code, error.params)}")
      | .ok application => k context (app.service context codecs application)
    finally dc.close

/-- LeanDB's migration gate at startup: a covered schema change is applied (and
reported), an uncovered one refuses with the gate's message naming every
`Entity.field`, and nothing is opened. Returns the exit code on refusal. -/
def gateDatabase (s : Type) [IsSchema s] (migrations : List LeanDb.SchemaMigration)
    (config : AppConfig) : IO (Option UInt32) := do
  match ← LeanDb.Gate.ensure config.database (LeanDb.Gate.Target.ofSchema s) migrations with
  | .error (.migrate why) =>
    IO.eprintln why
    return some LeanDb.Gate.refusedExit
  | .error error =>
    IO.eprintln s!"open {config.database}: {error.message}"
    return some 1
  | .ok outcome =>
    if outcome matches .applied .. then
      IO.println outcome.render
      (← IO.getStdout).flush
    return none

/-- An app executable over schema `s`: `LEANAPP_EMIT_CLIENT` emits the client;
`migrate --check` / `migrate` run LeanDB's `Gate.command?`; otherwise the startup gate, then
`serve`. `LEANAPP_*` overrides apply to all of them. -/
def runApp (s : Type) [IsSchema s] (migrations : List LeanDb.SchemaMigration)
    (emit : System.FilePath → IO Unit) (serve : AppConfig → IO Unit)
    (args : List String) (config : AppConfig := {}) : IO UInt32 := do
  if let some path ← IO.getEnv "LEANAPP_EMIT_CLIENT" then
    emit path
    return 0
  let config ← configure config
  if let some code ← LeanDb.Gate.command? config.database (LeanDb.Gate.Target.ofSchema s) migrations args then
    return code
  unless args.isEmpty do
    IO.eprintln s!"unsupported arguments {args}; expected none, `migrate --check` or `migrate`"
    return 2
  if let some code ← gateDatabase s migrations config then return code
  serve config
  return 0

/-- The app executable: `migrate --check` / `migrate`, or the startup gate then the server. -/
def NativeApp.main {s Profile} [IsSchema s] [LeanDb.Model.Entity Profile]
    (app : NativeApp s Profile) (args : List String) (config : AppConfig := {}) : IO UInt32 :=
  runApp s app.migrations app.emitClient
    (fun config => app.withService config fun _ service => LeanApi.serve service { port := config.port })
    args config

/-- A `main : IO Unit` (no arguments) still gets the startup gate and exits with the
gate's code on refusal. The `migrate` commands need `main (args)` with `NativeApp.main`. -/
def NativeApp.serve {s Profile} [IsSchema s] [LeanDb.Model.Entity Profile]
    (app : NativeApp s Profile) (config : AppConfig := {}) : IO Unit := do
  let code ← app.main [] config
  unless code == 0 do IO.Process.exit code.toUInt8

/-! ## Apps with no accounts

`app% Name where api := api` serves a portable `Api` with no credential and no sessions:
`PublicApp` has no profile type and no auth storage, rather than empty ones. Its operations
take no actor; see `assemblePublicCommandAt` for presented credentials and Origin. -/

/-- An app with no accounts: the api's routes over schema `s`, and the schema's migrations. -/
structure PublicApp (s : Type) [IsSchema s] : Type 1 where
  build : Contract.Http.Codecs → Ontology.Validation (Application s)
  /-- The published operations with their routes, in api order. -/
  descriptions : List (LeanApi.Publication.PublicOperation × Contract.Http.ErrorStatus × RouteBinding)
  /-- Declared schema migrations (`migration%`), handed to LeanDB's startup gate. -/
  migrations : List LeanDb.SchemaMigration := []
  /-- Extra GET routes (LeanReact's pages and assets); see `PageRoute`. -/
  pages : List PageRoute := []

def PublicApp.emitClient {s} [IsSchema s] (app : PublicApp s) (out : System.FilePath) : IO Unit :=
  emitRouteClient app.descriptions out

/-- Open the database, build the exact publication and run `k` with the service. -/
def PublicApp.withService {s} [IsSchema s] (app : PublicApp s) (config : AppConfig)
    (k : Service → IO α) : IO α := do
  let codecs ← contractCodecs
  let dc ← DbConns.open config.database (IsSchema.specs s) 2
  try
    match app.build codecs with
    | .error errors =>
      throw (IO.userError s!"app publication assembly failed: {errors.toList.map fun error => (error.code, error.params)}")
    | .ok publication =>
      let api := publication.routes dc (clock config.clockFile) executePrepared
      k (routerService (withPages api app.pages) publication.bodyFormat codecs)
  finally dc.close

/-- The executable: `migrate --check` / `migrate`, or the startup gate then the server. -/
def PublicApp.main {s} [IsSchema s] (app : PublicApp s) (args : List String) (config : AppConfig := {}) : IO UInt32 :=
  runApp s app.migrations app.emitClient
    (fun config => app.withService config fun service => LeanApi.serve service { port := config.port })
    args config

def PublicApp.serve {s} [IsSchema s] (app : PublicApp s) (config : AppConfig := {}) : IO Unit := do
  let code ← app.main [] config
  unless code == 0 do IO.Process.exit code.toUInt8

/-! ## `app%` -/

open Lean Elab Command Meta

private def generated (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .error error => throwError "app assembly: {error}\n{source}"
  | .ok command => elabCommand command

/-- `name := Entity.addField field (fill := v)` declares the migration (through LeanDB's
`migration%`) once `app%` has derived the native schema it needs; a bare name refers to a
`LeanDb.SchemaMigration` declared elsewhere. -/
syntax appMigration := ident (" := " term)?
syntax appMigrations := &"migrations" ":=" "[" appMigration,* "]"

/-- The endpoints of a portable `Api` declaration, in order: method, path template and the
published operation constant `f.operation`. -/
def apiEndpoints (apiName : Lean.Name) : CommandElabM (Array (String × String × Lean.Name)) := do
  let some value := (← getConstInfo apiName).value? | throwError "{apiName} has no definition"
  let env ← getEnv
  let mut result := #[]
  for constant in value.getUsedConstants do
    let some info := env.find? constant | continue
    unless info.type.getAppFn.isConstOf ``LeanApi.Core.Endpoint do continue
    let some body := info.value? | throwError "{constant} has no definition"
    let method ← match body.getAppFn.constName? with
      | some ``LeanApi.Core.Endpoint.post => pure "post"
      | some ``LeanApi.Core.Endpoint.get => pure "get"
      | _ => throwError "{constant} is not `Endpoint.post`/`Endpoint.get` of a published operation"
    let some template := body.getAppArgs.findSome? fun | .lit (.strVal path) => some path | _ => none
      | throwError "{constant}: no literal path"
    let some operation := body.getAppArgs.findSome? fun arg => match arg.getAppFn with
        | .const name _ => if name.getString! == "operation" then some name else none
        | _ => none
      | throwError "{constant}: no published operation"
    result := result.push (method, template, operation)
  return result

/-- The `migrations := […]` entries, as rooted `LeanDb.SchemaMigration` terms. Migrations need
the native entities, so an inline one is declared here, after the schema, under the app's
name, and recorded by LeanDB under its own short name. -/
def declareMigrations (appName : Lean.Name) (migrationTerms : Array Syntax) :
    CommandElabM (Array String) := do
  let root := fun n : Lean.Name => "_root_." ++ n.toString
  let mut migrations : Array String := #[]
  for migration in migrationTerms do
    let migrationName := migration[0].getId
    if migration[1].getNumArgs == 2 then
      let body ← liftCoreM <| PrettyPrinter.ppTerm ⟨migration[1][1]⟩
      generated ("namespace " ++ appName.toString)
      try
        withRef migration <| generated ("migration% " ++ migrationName.toString ++ " := " ++
          (body.pretty 100000))
      finally
        generated ("end " ++ appName.toString)
      migrations := migrations.push (root (appName ++ migrationName))
    else
      let resolved ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) migration[0])
      unless (← getConstInfo resolved).type.isConstOf ``LeanDb.SchemaMigration do
        throwErrorAt migration "{resolved} is not a migration (LeanDb.SchemaMigration)"
      migrations := migrations.push (root resolved)
  return migrations

/-- What an app with accounts authenticates with: its profile entity and the credential
entity the domain declared (`credential C.profile C.hash`). -/
structure Accounts where
  profile : Lean.Name
  credential : Lean.Name

/-- Declare the native app `appName` for the portable `Api` constant `api`: the native schema
(the domain entities of the api's namespace, plus the session table with accounts), the
migrations, and `appName : NativeApp …` (with accounts) or `appName : PublicApp …` (without).
Both `app%` forms run this; LeanReact's full-stack form runs it too, then sets `pages`. -/
def declareApiApp (appName api : Lean.Name) (accounts : Option Accounts) (migrationTerms : Array Syntax)
    (apiRef : Syntax) : CommandElabM Unit := do
  let root := fun n : Lean.Name => "_root_." ++ n.toString
  let base := root appName
  let schemaName := appName ++ `Database
  let schema := root schemaName
  let domain := api.getPrefix
  let place := if domain.isAnonymous then "the root namespace" else s!"namespace {domain}"
  let entities := (LeanDb.Model.Deriving.entityDeclarations.getState (← getEnv)).filter
    (fun entry => entry.name.getPrefix == domain)
  if entities.isEmpty then throwErrorAt apiRef "{api}: {place} declares no entities to store"
  if let some accounts := accounts then
    unless entities.any (·.name == accounts.credential) do
      throwErrorAt apiRef "{accounts.credential} is not an entity of {place}"
    unless entities.any (·.name == accounts.profile) do
      throwErrorAt apiRef "{accounts.profile} is not an entity of {place}"
  -- The schema: the domain's entities, and the app's session table when it has accounts. It is
  -- derived inside the app's namespace, so the instances it generates are named after the app
  -- and two apps' modules can be imported together.
  let sessionName := appName ++ `Session
  generated ("namespace " ++ appName.toString)
  try
    if let some accounts := accounts then
      generated ("native_session_entity% " ++ root sessionName ++ " for " ++ root accounts.profile)
    generated ("native_schema% Database := " ++ String.intercalate ", "
      (entities.toList.map (fun entry => root entry.name) ++ (if accounts.isSome then [root sessionName] else [])))
    if let some accounts := accounts then
      generated ("native_credential_storage% " ++ schema ++ " for " ++ root accounts.profile ++ " using " ++
        root accounts.credential ++ " session " ++ root sessionName)
  finally
    generated ("end " ++ appName.toString)
  let migrations ← declareMigrations appName migrationTerms
  -- One publication per endpoint.
  let mut entries : Array (Lean.Name × String × String) := #[]
  for (method, template, operation) in ← withRef apiRef (apiEndpoints api) do
    discard <| withRef apiRef (liftTermElabM (checkRoute method template operation))
    if entries.any (·.1 == operation) then
      throwErrorAt apiRef "{operation.getPrefix} is already routed; an operation has one route"
    let function := operation.getPrefix
    unless operation.getString! == "operation" && (← getEnv).contains (function ++ `Actor) do
      throwErrorAt apiRef "{function}: expected an operation of the api (`post \"/path\" f`)"
    let info ← getConstInfo operation
    let kind ← liftTermElabM <| whnf (info.type.getArg! 0)
    let query := kind.isConstOf ``Contract.OperationKind.query
    let binding := "(route_binding% " ++ method ++ " " ++ (Lean.Json.str template).compress ++ " " ++ root operation ++ ")"
    let requirements := "(" ++ root function ++ ".Requirements.infer)"
    -- The actor family `f.Actor`, read off the operation.
    let actor ← liftTermElabM do
      let family ← whnf (mkConst (function ++ `Actor))
      lambdaTelescope family fun _ body => do
        if body.isConstOf ``Unit then return none
        let rooted := body.replace fun
          | .const name levels => some (.const (`_root_ ++ name) levels)
          | _ => none
        let text ← withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.notation false) <| ppExpr rooted
        return some (body.isAppOfArity ``Option 1, text.pretty 100000, ← ppExpr body)
    let publish ← match accounts, actor with
      | none, none =>
        pure ("LeanApi.Native." ++ (if query then "assemblePublicQueryAt" else "assemblePublicCommandAt") ++
          " codecs " ++ binding ++ " " ++ root operation ++ " " ++ requirements)
      | none, some (_, _, shown) =>
        -- No accounts, no actor: an operation that needs a signed-in user cannot be served.
        throwErrorAt apiRef "{function} takes an actor ({shown}), but app% {appName} has no accounts, \
          so its operations must take none. Serve this api with a credential instead: declare \
          `credential C.profile C.hash` and add `authentication := P with C`."
      | some accounts, actor =>
        -- The Principal dictionaries are passed by name: their profile index is a class
        -- projection that instance search does not unfold.
        let actorArgs := match actor with
          | none => "(Actor := fun _ => Unit) "
          | some (optional, text, _) =>
            "(Actor := fun _ => " ++ text ++ ") (actorContext := LeanApi.Native." ++
              (if optional then "optionalPrincipalActor" else "principalActor") ++ " (P := " ++ root accounts.profile ++
              ") inferInstance rfl) "
        pure ("LeanApi.Native." ++ (if query then "assembleQueryAt" else "assembleCommandAt") ++ " " ++ actorArgs ++
          "context codecs " ++ binding ++ " " ++ root operation ++ " " ++ requirements)
    entries := entries.push (operation, binding, publish)
  let descriptions := "[" ++ String.intercalate ", " (entries.toList.map fun (operation, binding, _) =>
    "LeanApi.Native.describeAt " ++ binding ++ " " ++ root operation) ++ "]"
  let publications := "[" ++ String.intercalate ", " (entries.toList.map (·.2.2)) ++ "]"
  let migrationList := "[" ++ String.intercalate ", " migrations.toList ++ "]"
  match accounts with
  | some accounts =>
    let authOperations := "[" ++ String.intercalate ", " (entries.toList.map fun (operation, _, _) =>
      "(if " ++ root operation ++ ".metadata.establishesSession then some " ++ root operation ++ ".contract.identity else none)") ++
      "].filterMap id"
    generated ("def " ++ base ++ " : LeanApi.Native.NativeApp " ++ schema ++ " " ++ root accounts.profile ++ " := {\n" ++
      "  profile := LeanDb.Native.HasEntityStorage.storage\n  store := LeanApi.Native.Auth.HasStorage.storage\n" ++
      "  build := fun context codecs => LeanApi.Native.Application.create " ++ publications ++ "\n" ++
      "  descriptions := " ++ descriptions ++ "\n" ++
      "  authOperations := " ++ authOperations ++ "\n" ++
      "  migrations := " ++ migrationList ++ " }")
  | none =>
    generated ("def " ++ base ++ " : LeanApi.Native.PublicApp " ++ schema ++ " := {\n" ++
      "  build := fun codecs => (([" ++ String.intercalate ", " (entries.toList.map fun (operation, _, _) =>
        "LeanApi.Native.requireNoAccounts " ++ root operation) ++ "] : List (Ontology.Validation Unit)).forM id).bind fun _ =>\n" ++
      "    LeanApi.Native.Application.create " ++ publications ++ "\n" ++
      "  descriptions := " ++ descriptions ++ "\n" ++
      "  migrations := " ++ migrationList ++ " }")

/-- `app% Name where api := api`: serve a portable `Api` with no accounts. The schema is the
domain entities of the api's namespace (the root namespace for a root `api`); there is no
credential or session table. Every operation must take no actor: one that needs a signed-in
user (`SignedIn`, `Option SignedIn`) is an error here. -/
syntax (name := publicApp) "app% " ident " where " &"api" ":=" ident (appMigrations)? : command

/-- `app% Name where authentication := P with C api := api`: serve a portable `Api` with
accounts. `C` is the credential entity the domain declared with `credential C.profile C.hash`
(`P` its profile entity); the sessions are a library-owned table. -/
syntax (name := accountsApp) "app% " ident " where " &"authentication" ":=" ident " with " ident
  &"api" ":=" ident (appMigrations)? : command

@[command_elab publicApp]
def elabPublicApp : CommandElab := fun stx => withRef stx do
  let api ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[5])
  declareApiApp ((← getCurrNamespace) ++ stx[1].getId) api none
    ((stx[6].getOptional?.map (·[3].getSepArgs)).getD #[]) stx[5]

@[command_elab accountsApp]
def elabAccountsApp : CommandElab := fun stx => withRef stx do
  let profile ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[5])
  let credential ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[7])
  unless (← getEnv).contains (credential ++ `credentialLink) do
    throwErrorAt stx[7] "{credential} is not a declared credential; declare `credential {credential}.<profile field> {credential}.<hash field>`"
  let api ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[10])
  declareApiApp ((← getCurrNamespace) ++ stx[1].getId) api (some { profile, credential })
    ((stx[11].getOptional?.map (·[3].getSepArgs)).getD #[]) stx[10]

end LeanApi.Native
