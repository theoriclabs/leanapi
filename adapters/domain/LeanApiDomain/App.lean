import LeanApiDomain.Runtime
import LeanApiDomain.Routes
import LeanApiDomain.Principal
import LeanApiDomain.AuthDeriving
import LeanDb.Typed.Gate
import LeanReact.Domain
import LeanReact.Compiler
import LeanContract.Browser

namespace LeanApi.Domain
open LeanApi LeanDb LeanApp.Domain

structure Page where
  path : String
  exportName : String
  isScreen : Bool

def Page.describe (page : Page) : Lean.Json :=
  .mkObj [("path", .str page.path), ("exportName", .str page.exportName), ("screen", .bool page.isScreen)]

structure AppConfig where
  database : System.FilePath := "app.sqlite"
  port : UInt16 := 8080
  origin : Option String := none
  development : Bool := true
  browserDirectory : Option System.FilePath := none
  clockFile : Option System.FilePath := none

/-- The compiled browser entry of a LeanReact `App`: the LeanJS export names of its
component (`App.component`) and of the host-side `ShellProps`/`AppProps` constructors. -/
structure BrowserApp where
  component : String
  shell : String
  props : String

def BrowserApp.toJson (app : BrowserApp) : Lean.Json :=
  .mkObj [("component", .str app.component), ("shell", .str app.shell), ("props", .str app.props)]

namespace Browser

/-- What the browser host passes to a mounted `App` (compiled with LeanJS). `refresh` is the
app's own: `App.component` replaces it with its page-data reload. -/
def shellProps (generation : Nat) (currentGeneration : LeanReact.Action Nat)
    (framework : Contract.CallError Empty → LeanReact.Action Unit) (navigate : String → LeanReact.Action Unit)
    (authenticationChanged : LeanReact.Action Unit) : LeanReact.Domain.ShellProps :=
  { generation, currentGeneration, framework, navigate, refresh := pure (), authenticationChanged }

def appProps (shell : LeanReact.Domain.ShellProps) (location : String) (actor : Option String) :
    LeanReact.Domain.AppProps :=
  { shell, location, actor }

end Browser

structure NativeApp (s Profile : Type) [IsSchema s] [LeanApp.Domain.Entity Profile] : Type 1 where
  profile : LeanDb.Domain.EntityStorage s Profile
  store : Auth.Storage s Profile profile
  build : Context s Profile → Contract.Http.Codecs → Ontology.Validation (Application s)
  /-- The published operations with their routes, in route-list order. -/
  descriptions : List (LeanApp.PublicOperation × Contract.Http.ErrorStatus × RouteBinding)
  pages : List Page
  /-- Set when the pages come from a LeanReact `App`: the browser mounts its component. -/
  browserApp : Option BrowserApp := none
  /-- Relative to the build workspace root; see `NativeApp.browserCandidates`. -/
  browserDirectory : System.FilePath
  /-- The LeanJS export parsing the hydrated actor (milestone 1 pages); empty for an `App`. -/
  actorParser : String
  authOperations : List Contract.OperationId
  /-- Declared schema migrations (`migration%`), handed to LeanDB's startup gate. -/
  migrations : List LeanDb.SchemaMigration := []
  /-- The page shell's title. -/
  title : String := ""

def describeAt (binding : RouteBinding) (operation : LeanApp.Domain.Operation k Actor I O E) :
    LeanApp.PublicOperation × Contract.Http.ErrorStatus × RouteBinding :=
  ({ operation := operation.contract.describe, http := binding.publicHttp, metadata := {} },
    Contract.Http.ErrorStatus.ofOperation operation.contract (fun _ => 422), binding)

def describe (operation : LeanApp.Domain.Operation k Actor I O E) :
    LeanApp.PublicOperation × Contract.Http.ErrorStatus × RouteBinding :=
  describeAt (rpcBinding operation) operation

private def identityJson (identity : Contract.OperationId) : Lean.Json :=
  .mkObj [("namespace", .str identity.namespaceName), ("name", .str identity.name), ("version", .str identity.version)]

def NativeApp.emitClient {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (app : NativeApp s Profile) (out : System.FilePath) : IO Unit := do
  let codecs ← match Contract.Http.codecs with
    | .ok codecs => pure codecs
    | .error _ => throw (IO.userError "contract codec assembly failed")
  -- Explicit routes (templates, GET, plain bodies) go to the client as `ClientRoute`s, with the
  -- served manifest embedded verbatim; milestone 1 RPC apps keep the literal POST client.
  if app.descriptions.all (·.2.2.portable?.isSome) then
    Contract.Generate.emitClient (app.descriptions.map (·.1)) codecs (app.descriptions.map (·.2.1)) out "./runtime"
  else
    let routes := app.descriptions.map fun (operation, _, route) =>
      ({ identity := operation.operation.identity, method := route.methodName, path := route.path,
         params := route.params, body := match route.format with | .plain => "plain" | .envelope => "envelope" } :
        Contract.Generate.ClientRoute)
    let manifest : Lean.Json := .mkObj [("operations", .arr (app.descriptions.map fun (operation, _, route) =>
      operation.toJson.setObjVal! "http" route.toJson).toArray)]
    Contract.Generate.emitClient (app.descriptions.map (·.1)) codecs (app.descriptions.map (·.2.1)) out "./runtime"
      (routes := routes) (manifestOverride := some manifest)
  IO.FS.writeFile (out / "pages.json") (.mkObj [
    ("pages", .arr (app.pages.map Page.describe).toArray),
    ("app", (app.browserApp.map BrowserApp.toJson).getD .null),
    ("actorParser", .str app.actorParser),
    ("authentication", .arr (app.authOperations.map identityJson).toArray)] : Lean.Json).compress

private def clock (path : Option System.FilePath) : IO Env := do
  match path with
  | none => Env.fresh
  | some path =>
    let text ← IO.FS.readFile path
    let some now := text.trimAscii.toString.toNat? | throw (IO.userError "invalid injected clock")
    pure { now }

private def cli (config : AppConfig) : List String → IO AppConfig
  | [] => pure config
  | "--database" :: value :: rest => cli {config with database := value} rest
  | "--browser-dir" :: value :: rest => cli {config with browserDirectory := some value} rest
  | "--clock-file" :: value :: rest => cli {config with clockFile := some value} rest
  | "--port" :: value :: rest => do
    let some port := value.toNat? | throw (IO.userError "invalid port")
    if port == 0 || port > 65535 then throw (IO.userError "invalid port")
    cli {config with port := UInt16.ofNat port} rest
  | _ => throw (IO.userError "unsupported app arguments")

/-- The HTML shell every page shares: the app's title, its static page paths as navigation,
the bootstrap data and the compiled browser entry. -/
private def html (title : String) (navigation : List String) (bootstrap : Lean.Json) : Res :=
  let escape := fun (text : String) => ((text.replace "&" "&amp;").replace "<" "&lt;").replace "\"" "&quot;"
  let escaped := bootstrap.compress.replace "<" "\\u003c"
  let links := String.join (navigation.map fun path => "<a href=\"" ++ escape path ++ "\">" ++ escape path ++ "</a>")
  (Res.html ("<!doctype html><html><head><meta charset=\"utf-8\"><meta name=\"viewport\" content=\"width=device-width, initial-scale=1\"><title>" ++ escape title ++ "</title><style>body{font:16px system-ui;max-width:42rem;margin:3rem auto;padding:1rem}label{display:block;margin:1rem 0}input,select,textarea,button{font:inherit;padding:.5rem}button{margin:.5rem}nav{display:flex;gap:1rem}[role=alert]{color:#a21}</style></head><body><nav>" ++ links ++ "</nav><main id=\"root\"></main><script type=\"application/json\" id=\"leanapp-bootstrap\">" ++ escaped ++ "</script><script type=\"module\" src=\"/assets/app.mjs\"></script></body></html>")).setHeader "cache-control" "private, no-store"

/-- A navigation request: the client lists `text/html` in Accept. `fetch` defaults to
`*/*`, and curl to `*/*`, so both reach the endpoint. -/
def acceptsHtml (req : Req) : Bool :=
  (req.headerAll "accept").any fun line => (line.splitOn ",").any fun range =>
    ((range.splitOn ";").headD "").trimAscii.toString.toLower == "text/html"

def NativeApp.service {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (app : NativeApp s Profile) (context : Context s Profile) (codecs : Contract.Http.Codecs)
    (publication : Application s) (browser : System.FilePath) : Service :=
  let page : Req → IO Res := fun req => do
    match ← context.dc.read (Read.runPrepared (do context.fresh) (fun env =>
        Auth.resolve (Scope := Unit) context.cookies env req context.store.live)) with
    | .error .busy => return frameworkReply codecs (Native.fault (Error := Empty) "storage.busy" 503)
    | .error .stopped | .ok (.error _) => return frameworkReply codecs (Native.fault (Error := Empty) "storage.unavailable")
    | .ok (.ok (.error fault)) => return databaseReply fault
    | .ok (.ok (.ok (.error error))) => return frameworkReply codecs error
    | .ok (.ok (.ok (.ok actor))) =>
      let actor := actor.map (fun row => (LeanApp.Domain.refCodec (T := Profile)).encode row.id) |>.getD .null
      let navigation := (app.pages.map (·.path)).filter fun path => !path.contains ':' && !path.contains '{'
      return html app.title navigation (.mkObj [("actor", actor), ("csrfCookie", .str context.cookies.csrfName)])
  let asset := Route.get "/assets/app.mjs" fun _ => do
    return (Res.bytes (← IO.FS.readBinFile (browser / "app.mjs")) "text/javascript; charset=utf-8").setHeader "cache-control" "private, no-store"
  let api := publication.routes context.dc context.fresh executePrepared
  -- A page and a GET endpoint may share a path (say `/books/:book`): a browser navigation
  -- (Accept: text/html) gets the page, any other client the endpoint.
  let shape := fun (template : String) => (parseTemplate template).toOption.map (·.map Seg.shape)
  let pageRoutes := app.pages.map fun p =>
    let template := ({ path := p.path : RouteBinding }).routerTemplate
    match api.find? (fun r => r.method == .get && shape r.template == shape template) with
    | some endpoint =>
      let negotiated : App := fun req => if acceptsHtml req then page req else endpoint.handler req
      { endpoint with handler := negotiated }
    | none => Route.get template page
  let api := api.filter fun r => !(r.method == .get &&
    app.pages.any (fun p => shape ({ path := p.path : RouteBinding }).routerTemplate == shape r.template))
  let routes := api ++ pageRoutes ++ (if app.pages.isEmpty then [] else [asset])
  -- Apps with plain routes answer framework failures, unknown paths included, in the
  -- `{"error": …}` envelope; milestone 1 RPC apps keep their Contract replies.
  let format : BodyFormat := if publication.bindings.any (·.format == .plain) then .plain else .envelope
  let router := Router.build! routes
  let router := if format == .plain then
      { router with notFound := fun _ => pure (envelopeFailure (Native.fault (Error := Empty) "route.not_found" 404)) }
    else router
  { Service.ofRouter router with
    bodyTooLarge := fun _ _ => failureReply format codecs (Native.fault (Error := Empty) "request.body_too_large" 413)
    errorResponse := fun _ => failureReply format codecs (Native.fault (Error := Empty) "infrastructure.unavailable")
    logErrors := false }

/-- Where the compiled browser bundle may be, in order: an explicit directory (config or
`LEANAPP_BROWSER_DIR`), the build workspace of this executable (`.lake/build/bin/<exe>`
four levels up), then the working directory. No environment variable is needed when the
executable runs from its build tree, e.g. under `lake exe`. -/
def NativeApp.browserCandidates {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (app : NativeApp s Profile) (config : AppConfig) : IO (List System.FilePath) := do
  match config.browserDirectory with
  | some directory => return [directory]
  | none =>
    let executable ← IO.appPath
    let workspace := executable.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)
    return (workspace.map (· / app.browserDirectory)).toList ++ [app.browserDirectory]

def NativeApp.findBrowser {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (app : NativeApp s Profile) (config : AppConfig) : IO System.FilePath := do
  let candidates ← app.browserCandidates config
  for candidate in candidates do
    if ← (candidate / "app.mjs").pathExists then return candidate
  throw (IO.userError s!"compiled browser entry missing (looked for app.mjs in {candidates}); \
    build the browser bundle or set LEANAPP_BROWSER_DIR")

/-- `LEANAPP_*` development overrides, applied over the authored configuration. -/
def NativeApp.configure (config : AppConfig) : IO AppConfig := do
  let mut args := []
  for (key, option) in [("LEANAPP_DATABASE", "--database"), ("LEANAPP_BROWSER_DIR", "--browser-dir"),
      ("LEANAPP_CLOCK_FILE", "--clock-file"), ("LEANAPP_PORT", "--port")] do
    if let some value ← IO.getEnv key then args := args ++ [option, value]
  cli config args

/-- Open the database and auth context, build the exact publication and run `k` with the
service. `serve` listens with it; tests drive it through the in-process HTTP transport. -/
def NativeApp.withService {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (app : NativeApp s Profile) (config : AppConfig)
    (k : Context s Profile → Service → IO α) : IO α := do
    let browser ← if app.pages.isEmpty then pure (config.browserDirectory.getD app.browserDirectory)
      else app.findBrowser config
    let cookies ← match Auth.CookieConfig.create
        (config.origin.getD s!"http://127.0.0.1:{config.port.toNat}") config.development with
      | .ok config => pure config
      | .error _ => throw (IO.userError "invalid app cookie origin")
    let codecs ← match Contract.Http.codecs with
      | .ok codecs => pure codecs
      | .error _ => throw (IO.userError "contract codec assembly failed")
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
      | .error errors => throw (IO.userError s!"app publication assembly failed: {errors.toList.map (·.code)}")
      | .ok application => k context (app.service context codecs application browser)
    finally dc.close

/-- LeanDB's migration gate at startup: a covered schema change is applied (and
reported), an uncovered one refuses with the gate's message naming every
`Entity.field`, and nothing is opened. Returns the exit code on refusal. -/
def NativeApp.gate {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (app : NativeApp s Profile) (config : AppConfig) : IO (Option UInt32) := do
  match ← LeanDb.Gate.ensure config.database (LeanDb.Gate.Target.ofSchema s) app.migrations with
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

/-- The app executable: `migrate --check` / `migrate` (LeanDB's `Gate.command?`), or the
startup gate then the server. `LEANAPP_*` overrides apply to both. -/
def NativeApp.main {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (app : NativeApp s Profile) (args : List String) (config : AppConfig := {}) : IO UInt32 := do
  if let some path ← IO.getEnv "LEANAPP_EMIT_CLIENT" then
    app.emitClient path
    return 0
  let config ← NativeApp.configure config
  if let some code ← LeanDb.Gate.command? config.database (LeanDb.Gate.Target.ofSchema s) app.migrations args then
    return code
  unless args.isEmpty do
    IO.eprintln s!"unsupported arguments {args}; expected none, `migrate --check` or `migrate`"
    return 2
  if let some code ← app.gate config then return code
  app.withService config fun _ service => LeanApi.serve service { port := config.port }
  return 0

/-- A `main : IO Unit` (no arguments) still gets the startup gate and exits with the
gate's code on refusal. The `migrate` commands need `main (args)` with `NativeApp.main`. -/
def NativeApp.serve {s Profile} [IsSchema s] [LeanApp.Domain.Entity Profile]
    (app : NativeApp s Profile) (config : AppConfig := {}) : IO Unit := do
  let code ← app.main [] config
  unless code == 0 do IO.Process.exit code.toUInt8

open Lean Elab Command Meta

private def generated (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .error error => throwError "app assembly: {error}\n{source}"
  | .ok command => elabCommand command

declare_syntax_cat appPage
syntax str " => " ident : appPage
/-- `post "/books/:book/loans" Library.borrow`, `get "/orders/:order" Shop.orderPage`. -/
declare_syntax_cat appRoute
syntax ident str ident : appRoute
/-- `name := Entity.addField field (fill := v)` declares the migration (through LeanDB's
`migration%`) once `app%` has derived the native schema it needs; a bare name refers to a
`LeanDb.SchemaMigration` declared elsewhere. -/
syntax appMigration := ident (" := " term)?
syntax appMigrations := &"migrations" ":=" "[" appMigration,* "]"
/-- `api := api`: serve a portable `Api` (`def api : Api := [post "/x" f, get "/y/:id" g]`). -/
syntax appApi := &"api" ":=" ident
/-- Milestone 1 form: routes derived from operation names (`POST /api/<ns>/<name>`, envelope). -/
syntax (name := domainApp) "app% " ident " where " &"authentication" ":=" ident (" with " ident)?
  &"operations" ":=" "[" ident,* "]" &"pages" ":=" "[" appPage,* "]" (appApi)? (appMigrations)? : command
/-- Explicit route list. Only the listed entries are routable, in the manifest and in the client.
`migrations := [m, …]` lists the domain's `migration%` declarations for the startup gate. -/
syntax (name := domainAppRoutes) "app% " ident " where " &"authentication" ":=" ident (" with " ident)?
  &"routes" ":=" "[" appRoute,* "]" &"pages" ":=" "[" appPage,* "]" (appApi)? (appMigrations)? : command

/-- One published entry: the operation, its binding term and its publication term. -/
private structure AppEntry where
  operation : Lean.Name
  binding : String
  publish : String

/-- The endpoints of a portable `Api` declaration, in order: method, path template and the
published operation constant `f.operation`. -/
def apiEndpoints (apiName : Lean.Name) : CommandElabM (Array (String × String × Lean.Name)) := do
  let some value := (← getConstInfo apiName).value? | throwError "{apiName} has no definition"
  let env ← getEnv
  let mut result := #[]
  for constant in value.getUsedConstants do
    let some info := env.find? constant | continue
    unless info.type.getAppFn.isConstOf ``LeanApp.Domain.Endpoint do continue
    let some body := info.value? | throwError "{constant} has no definition"
    let method ← match body.getAppFn.constName? with
      | some ``LeanApp.Domain.Endpoint.post => pure "post"
      | some ``LeanApp.Domain.Endpoint.get => pure "get"
      | _ => throwError "{constant} is not `Endpoint.post`/`Endpoint.get` of a published operation"
    let some template := body.getAppArgs.findSome? fun | .lit (.strVal path) => some path | _ => none
      | throwError "{constant}: no literal path"
    let some operation := body.getAppArgs.findSome? fun arg => match arg.getAppFn with
        | .const name _ => if name.getString! == "operation" then some name else none
        | _ => none
      | throwError "{constant}: no published operation"
    result := result.push (method, template, operation)
  return result

/-- What an `app%` declaration assembles, read off its clauses or off a LeanReact `App`. -/
private structure AppSource where
  name : TSyntax `ident
  /-- The milestone 1 `Account`, or the profile entity of an authored credential. -/
  account : Lean.Name
  accountRef : Syntax
  /-- The authored credential entity (`credential C.profile C.hash` in the domain). -/
  credential : Option (Lean.Name × Syntax) := none
  explicitRoutes : Bool
  entryTerms : Array Syntax := #[]
  pageTerms : Array Syntax := #[]
  /-- A portable `Api` constant, and the syntax that named it. -/
  api : Option (Lean.Name × Syntax) := none
  /-- A LeanReact `App` whose pages are served (its `api` is `api` above). -/
  reactApp : Option Lean.Name := none
  migrationTerms : Array Syntax := #[]
  ref : Syntax

private def elabAppCore (src : AppSource) : CommandElabM Unit := withRef src.ref do
    let name := src.name
    let accountName := src.account
    let authoredCredential := src.credential
    let entryTerms := src.entryTerms
    let pageTerms := src.pageTerms
    let migrationTerms := src.migrationTerms
    let explicitRoutes := src.explicitRoutes
    let accountType := (← getConstInfo accountName).type
    let profile ← match authoredCredential with
      | some _ => pure accountName
      | none =>
        unless accountType.isAppOfArity ``Account 2 do
          throwErrorAt src.accountRef "expected an Account, or `Profile with Credential` for an authored credential entity"
        let .const profile _ := accountType.getArg! 0 | throwErrorAt src.accountRef "expected declared profile"
        pure profile
    let appName := (← getCurrNamespace) ++ name.getId
    let root := fun n : Lean.Name => "_root_." ++ n.toString
    let base := root appName
    let schemaName := appName ++ `Database
    let schema := root schemaName
    let entities := (LeanApp.Domain.Deriving.entityDeclarations.getState (← getEnv)).filter
      (fun entry => entry.name.getPrefix == profile.getPrefix)
    if entities.isEmpty then throwError "empty domain entity closure"
    match authoredCredential with
    | some (credential, credentialRef) =>
      unless entities.any (·.name == credential) do
        throwErrorAt credentialRef "{credential} is not an entity of {profile}'s domain"
      let sessionName := appName ++ `Session
      generated ("native_session_entity% " ++ root sessionName ++ " for " ++ root profile)
      generated ("native_schema% " ++ schemaName.toString ++ " := " ++ String.intercalate ", "
        (entities.toList.map (fun entry => entry.name.toString) ++ [sessionName.toString]))
      generated ("native_credential_storage% " ++ schema ++ " for " ++ root profile ++ " using " ++ root credential ++
        " session " ++ root sessionName)
    | none =>
      generated ("native_auth_entities% " ++ root accountName)
      generated ("native_schema% " ++ schemaName.toString ++ " := " ++ String.intercalate ", "
        (entities.toList.map (fun entry => entry.name.toString) ++ [accountName.toString ++ ".Native.Credential", accountName.toString ++ ".Native.Session"]))
      generated ("native_auth_storage% " ++ schema ++ " for " ++ root accountName)
    -- Migrations need the native entities, so they are declared here, under the app's
    -- name, and recorded by LeanDB under their own short name.
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
    let signUp := accountName ++ `signUp
    let signIn := accountName ++ `signIn
    let publishTerm := fun (operation : Lean.Name) (binding : String) => do
      let op := root operation
      if operation == signUp then
        return "LeanApi.Domain.publishSignUpAt context codecs " ++ binding ++ " " ++ root accountName ++ " (" ++ op ++ ".Requirements.infer)"
      if operation == signIn then
        return "LeanApi.Domain.publishSignInAt context codecs " ++ binding ++ " " ++ root accountName ++ " (" ++ op ++ ".Requirements.infer)"
      let info ← getConstInfo operation
      unless info.type.isAppOfArity ``LeanApp.Domain.Operation 5 do throwError "expected domain Operation"
      let kind ← liftTermElabM <| whnf (info.type.getArg! 0)
      let function := if kind.isConstOf ``Contract.OperationKind.query then "assembleQueryAt" else "assembleCommandAt"
      -- A plain operation `f` (DDD-LR-05) is `f.operation`, with `f.Requirements.infer` and an
      -- actor family `f.Actor` that instance search cannot unfold, so it is passed explicitly.
      let plain := operation.getString! == "operation" && (← getEnv).contains (operation.getPrefix ++ `Actor)
      let requirements := root (if plain then operation.getPrefix else operation) ++ ".Requirements.infer"
      let actor ← if !plain then pure "" else liftTermElabM do
        let family ← whnf (mkConst (operation.getPrefix ++ `Actor))
        lambdaTelescope family fun _ body => do
          let rooted := body.replace fun
            | .const name levels => some (.const (`_root_ ++ name) levels)
            | _ => none
          let text ← withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.notation false) <| ppExpr rooted
          -- The Principal dictionaries are passed by name: their profile index is a class
          -- projection that instance search does not unfold.
          let context := if body.isConstOf ``Unit then ""
            else if body.isAppOfArity ``Option 1 then "(actorContext := LeanApi.Domain.Native.optionalPrincipalActor (P := " ++ root profile ++ ") inferInstance rfl) "
            else "(actorContext := LeanApi.Domain.Native.principalActor (P := " ++ root profile ++ ") inferInstance rfl) "
          pure ("(Actor := fun _ => " ++ text.pretty 100000 ++ ") " ++ context)
      return "LeanApi.Domain." ++ function ++ " " ++ actor ++ "context codecs " ++ binding ++ " " ++ op ++ " (" ++ requirements ++ ")"
    let mut entries : Array AppEntry := #[]
    if explicitRoutes then
      for entry in entryTerms do
        let method := entry[0].getId.toString
        let some template := entry[1].isStrLit? | throwErrorAt entry[1] "expected a path template"
        let operation ← withRef entry[2] (resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) entry[2]))
        -- The same check `route_binding%` runs, reported at this entry.
        discard <| withRef entry (liftTermElabM (checkRoute method template operation))
        if entries.any (·.operation == operation) then
          throwErrorAt entry "{operation} is already routed; an operation has one route"
        let binding := "(route_binding% " ++ method ++ " " ++ (Lean.Json.str template).compress ++ " " ++ root operation ++ ")"
        entries := entries.push ⟨operation, binding, ← withRef entry (publishTerm operation binding)⟩
      -- A portable `Api`: each `api.f : Endpoint …` is `Endpoint.post|get "/path" f.operation`.
      if let some (apiName, clause) := src.api then
        for (method, template, operation) in ← withRef clause (apiEndpoints apiName) do
          discard <| withRef clause (liftTermElabM (checkRoute method template operation))
          if entries.any (·.operation == operation) then
            throwErrorAt clause "{operation.getPrefix} is already routed; an operation has one route"
          let binding := "(route_binding% " ++ method ++ " " ++ (Lean.Json.str template).compress ++ " " ++ root operation ++ ")"
          entries := entries.push ⟨operation, binding, ← withRef clause (publishTerm operation binding)⟩
    else
      if let some (_, clause) := src.api then throwErrorAt clause "`api := …` needs the `routes := […]` form"
      if let some (_, credentialRef) := authoredCredential then
        throwErrorAt credentialRef "an authored credential needs the `routes := […]` form"
      for operation in #[signUp, signIn] do
        let binding := "(LeanApi.Domain.rpcBinding " ++ root operation ++ ")"
        entries := entries.push ⟨operation, binding, ← publishTerm operation binding⟩
      for operation in entryTerms do
        let resolved ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) operation)
        let binding := "(LeanApi.Domain.rpcBinding " ++ root resolved ++ ")"
        entries := entries.push ⟨resolved, binding, ← withRef operation (publishTerm resolved binding)⟩
    let browser := ".lake/ddd-browser/" ++ appName.toString
    let mut pageValues := #[]
    let mut exports := #[`Contract.Browser.jsonObject, `Contract.Browser.jsonEntries,
      `Contract.Browser.jsonNumber, `Contract.Browser.frameworkError, `Contract.Browser.decodeErrors]
    let mut browserApp := "none"
    match src.reactApp with
    | some reactApp =>
      -- A LeanReact `App`: the browser mounts `App.component`, which routes its own pages.
      let component := appName ++ `browserApp
      generated ("def " ++ root component ++ " (client : Contract.Interpreter LeanReact.Action) (requestClient : LeanReact.ResourceRequest → Contract.Interpreter LeanReact.Action) : LeanReact.Component LeanReact.Domain.AppProps := LeanReact.Domain.App.component " ++ root reactApp ++ " client (some requestClient)")
      exports := exports ++ #[component, ``Browser.shellProps, ``Browser.appProps]
      browserApp := "some { component := " ++ (Lean.Json.str component.toString).compress ++
        ", shell := " ++ (Lean.Json.str (``Browser.shellProps).toString).compress ++
        ", props := " ++ (Lean.Json.str (``Browser.appProps).toString).compress ++ " }"
    | none =>
      exports := exports.push (appName ++ `actorRef)
      generated ("def " ++ base ++ ".actorRef (key : String) := LeanApp.Domain.Ref.parse (T := " ++ root profile ++ ") key")
    for i in [:pageTerms.size] do
      let path : TSyntax `str := ⟨pageTerms[i]![0]⟩
      let value : TSyntax `ident := ⟨pageTerms[i]![2]⟩
      let resolved ← resolveGlobalConstNoOverload value
      let type := (← getConstInfo resolved).type
      let isScreen := type.getAppFn.isConstOf ``LeanReact.Domain.ScreenSpec
      unless isScreen || type.getAppFn.isConstOf ``LeanReact.Domain.FormSpec do throwErrorAt value "expected derived form or screen"
      let exportName := appName ++ Lean.Name.mkSimple ("page" ++ toString i)
      if isScreen then
        generated ("def " ++ root exportName ++ " (client : Contract.Interpreter LeanReact.Action) (requestClient : LeanReact.ResourceRequest → Contract.Interpreter LeanReact.Action) := " ++ root resolved ++ ".component (A := " ++ root profile ++ ") client (some requestClient)")
      else
        generated ("def " ++ root exportName ++ " (client : Contract.Interpreter LeanReact.Action) (requestClient : LeanReact.ResourceRequest → Contract.Interpreter LeanReact.Action) : LeanReact.Component LeanReact.Domain.ShellProps := LeanReact.component fun context => do\n  let shell : LeanReact.Domain.Shell := { toShellProps := context, client, requestClient := some requestClient }\n  let model ← LeanReact.Domain.useDomainForm " ++ root resolved ++ " shell\n  pure (LeanReact.Domain.FormSpec.render " ++ root resolved ++ " model)")
      exports := exports.push exportName
      pageValues := pageValues.push ("{ path := " ++ (Lean.Json.str path.getString).compress ++ ", exportName := " ++ (Lean.Json.str exportName.toString).compress ++ ", isScreen := " ++ toString isScreen ++ " }")
    -- An `App`'s pages are its own `path ==> page` list, read when the server starts.
    let pagesTerm := match src.reactApp with
      | some reactApp => "(LeanReact.Domain.App.pages " ++ root reactApp ++ ").map fun page => { path := page.path, exportName := \"\", isScreen := false }"
      | none => "[" ++ String.intercalate ", " pageValues.toList ++ "]"
    -- The browser shell treats a call as signing in when it does: milestone 1 names its auth
    -- operations; an authored credential's are those whose flow starts a session.
    let authOperations := if authoredCredential.isSome then
        "[" ++ String.intercalate ", " (entries.toList.map fun entry =>
          "(if " ++ root entry.operation ++ ".metadata.establishesSession then some " ++ root entry.operation ++ ".contract.identity else none)") ++ "].filterMap id"
      else
        "[" ++ String.intercalate ", " ((entries.filter (fun entry => entry.operation == signUp || entry.operation == signIn)).toList.map
          (fun entry => root entry.operation ++ ".contract.identity")) ++ "]"
    -- The page title: the root module of the `App`'s declaration (`Shop.Views` gives `Shop`),
    -- else the app's own name.
    let title ← match src.reactApp with
      | some reactApp => do
        let env ← getEnv
        let module := match env.getModuleIdxFor? reactApp with
          | some index => env.header.moduleNames[index.toNat]!
          | none => env.mainModule
        pure module.getRoot.toString
      | none => pure (if appName.getPrefix.isAnonymous then appName.toString else appName.getPrefix.toString)
    generated ("def " ++ base ++ " : LeanApi.Domain.NativeApp " ++ schema ++ " " ++ root profile ++ " := {\n" ++
      "  profile := LeanDb.Domain.HasEntityStorage.storage\n  store := LeanApi.Domain.Auth.HasStorage.storage\n" ++
      "  build := fun context codecs => LeanApi.Domain.Application.create [" ++ String.intercalate ", " (entries.toList.map (·.publish)) ++ "]\n" ++
      "  descriptions := [" ++ String.intercalate ", " (entries.toList.map fun entry => "LeanApi.Domain.describeAt " ++ entry.binding ++ " " ++ root entry.operation) ++ "]\n" ++
      "  «pages» := " ++ pagesTerm ++ "\n" ++
      "  browserApp := " ++ browserApp ++ "\n" ++
      "  browserDirectory := " ++ (Lean.Json.str browser).compress ++ "\n" ++
      "  actorParser := " ++ (Lean.Json.str (if src.reactApp.isSome then "" else (appName ++ `actorRef).toString)).compress ++ "\n" ++
      "  authOperations := " ++ authOperations ++ "\n" ++
      "  migrations := [" ++ String.intercalate ", " migrations.toList ++ "]\n" ++
      "  title := " ++ (Lean.Json.str title).compress ++ " }")
    -- The browser modules exist only for an app with pages.
    unless pageTerms.isEmpty && src.reactApp.isNone do
      liftCoreM do
        IO.FS.createDirAll browser
        LeanJS.writeModule (System.FilePath.mk browser / "domain.mjs") exports
          (LeanReact.Compiler.options "./runtime/leanjs-react.mjs")

/-- The clauses of the milestone 1 and explicit-route forms. -/
private def AppSource.ofSyntax (stx : Syntax) (explicitRoutes : Bool) : CommandElabM AppSource := do
  let account : TSyntax `ident := ⟨stx[5]⟩
  let accountName ← resolveGlobalConstNoOverload account
  -- `authentication := Profile with Credential`: an authored credential entity, declared
  -- explicitly. Without `with`, `authentication` names a milestone 1 `Account`.
  let credential ← if stx[6].getNumArgs == 2 then
      pure (some (← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[6][1]), stx[6][1]))
    else pure none
  let api ← match stx[17].getOptional? with
    | some clause => pure (some (← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) clause[2]), clause))
    | none => pure none
  return { name := ⟨stx[1]⟩, account := accountName, accountRef := account, credential, explicitRoutes,
           entryTerms := stx[10].getSepArgs, pageTerms := stx[15].getSepArgs, api,
           migrationTerms := (stx[18].getOptional?.map (·[3].getSepArgs)).getD #[], ref := stx }

@[command_elab domainApp]
def elabApp : CommandElab := fun stx => do elabAppCore (← AppSource.ofSyntax stx false)

@[command_elab domainAppRoutes]
def elabAppRoutes : CommandElab := fun stx => do elabAppCore (← AppSource.ofSyntax stx true)

/-- `app := app`: serve a LeanReact `App { api, pages }`. Its `api` must be a declared
`def … : Api`; its pages are served as the app's HTML routes and routed in the browser by
`App.component`. Authentication is the domain's own: the one entity declared with
`credential C.profile C.hash` next to the api, and the api's operations that start a
session (`Auth.startSession`). -/
syntax (name := domainReactApp) "app% " ident " where " &"app" ":=" ident (appMigrations)? : command

/-- The `api` of a LeanReact `App` declared as `def app : App where api := api; pages := …`. -/
def reactAppApi (app : Lean.Name) : CommandElabM Lean.Name := do
  let info ← getConstInfo app
  unless info.type.isConstOf ``LeanReact.Domain.App do throwError "{app} is not a LeanReact `App`"
  let some value := info.value? | throwError "{app} has no definition"
  let value := value.consumeMData
  unless value.isAppOfArity ``LeanReact.Domain.App.mk 2 do
    throwError "{app} must be a structure instance `\{ api := …, pages := … }`"
  let .const api _ := (value.getArg! 0).consumeMData
    | throwError "{app}: `api` must name a declared `def … : Api`"
  return api

/-- The domain's credential entity and its profile: the one entity of `domain` with a
`credential` declaration (`C.credentialLink : CredentialLink C P`). -/
def domainCredential (domain : Lean.Name) : CommandElabM (Lean.Name × Lean.Name) := do
  let env ← getEnv
  let entities := (LeanApp.Domain.Deriving.entityDeclarations.getState env).filter (·.name.getPrefix == domain)
  let credentials := entities.filter fun entry => env.contains (entry.name ++ `credentialLink)
  match credentials.toList with
  | [entry] =>
    let type := (← getConstInfo (entry.name ++ `credentialLink)).type
    unless type.isAppOfArity ``LeanApp.Domain.CredentialLink 2 do
      throwError "{entry.name}.credentialLink is not a `CredentialLink`"
    let .const profile _ := type.getArg! 1 | throwError "{entry.name}.credentialLink: expected a profile entity"
    return (profile, entry.name)
  | [] => throwError "the app's domain declares no credential; add `credential C.profile C.hash` for its password table"
  | many => throwError "the app's domain declares more than one credential: {many.map (·.name)}"

@[command_elab domainReactApp]
def elabReactApp : CommandElab := fun stx => do
  let appRef := stx[5]
  let reactApp ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) appRef)
  let api ← withRef appRef (reactAppApi reactApp)
  let (profile, credential) ← withRef appRef (domainCredential api.getPrefix)
  elabAppCore { name := ⟨stx[1]⟩, account := profile, accountRef := appRef, credential := some (credential, appRef),
                explicitRoutes := true, api := some (api, appRef), reactApp := some reactApp,
                migrationTerms := (stx[6].getOptional?.map (·[3].getSepArgs)).getD #[], ref := stx }

end LeanApi.Domain
