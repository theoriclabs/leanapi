/-
  The architecture of LeanAPI, checked against its imports.

  `Part` names the parts, `partOf` puts every module in one, and `design`
  says which part may use which. `conforms` is a theorem: every import in
  this build follows the design. The theorems after it are the rules the
  design exists for, and they hold for every chain of imports, not just
  single ones.

  "Reaches" is through LeanAPI's own modules: the graph has an edge for
  each import a LeanAPI module makes, and stops at other packages. What
  `Std.Http` or LeanDB import is their business.
-/
import Architecture.Graph
import LeanApi

namespace Architecture.Framework

open Architecture Lean

/-- The parts of LeanAPI, and the packages it builds on. -/
inductive Part where
  /-- Base64 and URL encoding. -/
  | util
  /-- Requests and responses as values, and decoding their parts. -/
  | wire
  /-- The authenticated actor, `Auth`: made by authentication, taken by
      handlers, database programs and row policies. -/
  | actor
  /-- Routes, the router, OpenAPI. -/
  | routing
  /-- Middleware, and a service: the router wrapped in its middleware. -/
  | middleware
  /-- Credentials: Basic, bearer tokens, JWT, password hashing. -/
  | credentials
  /-- The property library: systems, invariants, noninterference, idempotence, the evidence registry. -/
  | props
  /-- Typed endpoints and `api!`, with the theorems about every typed API. -/
  | endpoints
  /-- Endpoints over LeanDB programs. -/
  | database
  /-- Threads for blocking work (SQLite), with backpressure. -/
  | workers
  /-- The server: HTTP on sockets, and the test client. -/
  | server
  /-- `app.listen`, and the `LeanApi` module that imports everything. -/
  | assembly
  /-- Lean's core and standard library. -/
  | lean
  /-- `Std.Async` and `Std.Sync`: tasks, timers, mutexes. -/
  | async
  /-- `Std.Http`: HTTP/1.1 on sockets. -/
  | transport
  /-- LeanCrypto. -/
  | crypto
  /-- LeanDB. -/
  | leandb
  deriving DecidableEq, Repr

open Part

/-- Which part each module is in: the first rule whose name is a prefix of
    the module's. -/
def rules : List (Name × Part) := [
  (`LeanApi.Util,               util),
  (`LeanApi.Http.Request,       wire),
  (`LeanApi.Http.Response,      wire),
  (`LeanApi.Http.Extract,       wire),
  (`LeanApi.Http.Multipart,     wire),
  (`LeanApi.Auth.Actor,         actor),
  (`LeanApi.Http.Router,        routing),
  (`LeanApi.Http.OpenApi,       routing),
  (`LeanApi.Http.Middleware,    middleware),
  (`LeanApi.Http.Service,       middleware),
  (`LeanApi.Http.Features,      middleware),
  (`LeanApi.Http.Typed,         middleware),
  (`LeanApi.Auth,               credentials),
  (`LeanApi.Props,              props),
  (`LeanApi.Proofs,             props),
  (`LeanApi.Http.Idempotency,   endpoints),
  (`LeanApi.Http.Endpoint,      endpoints),
  (`LeanApi.Http.DbEndpoint,    database),
  (`LeanApi.Http.DbProblem,     database),
  (`LeanApi.Runtime.Blocking,   workers),
  (`LeanApi.Runtime,            server),
  (`LeanApi.Http.Listen,        assembly),
  (`LeanApi,                    assembly),
  (`Std.Http,                   transport),
  (`Std.Async,                  async),
  (`Std.Sync,                   async),
  (`LeanCrypto,                 crypto),
  (`LeanDb,                     leandb),
  (`Init,                       lean),
  (`Std,                        lean),
  (`Lean,                       lean)]

def partOf (m : Name) : Option Part :=
  (rules.find? fun r => r.1.isPrefixOf m).map (·.2)

/-- The design: which part may use which, directly. A part may also use
    whatever those parts may use. -/
def design : Graph Part := ⟨[
  (util, lean),
  (wire, util),
  (routing, wire),
  (middleware, routing), (middleware, async),
  (credentials, wire), (credentials, crypto),
  (props, routing),
  (endpoints, middleware), (endpoints, credentials), (endpoints, actor), (endpoints, props),
  (database, endpoints), (database, workers), (database, leandb),
  (workers, async),
  (server, middleware), (server, transport),
  (assembly, database), (assembly, server),
  (actor, lean), (async, lean), (crypto, lean), (leandb, lean), (transport, lean)]⟩

/-- LeanAPI's imports, as this build compiled them. -/
def imports : Graph Name := imports% LeanApi

/-- **Every import follows the design.** Checked for each import by the
    kernel. A new module in no part, or an import the design does not
    allow, fails the build and is named in the error. -/
theorem conforms : imports.Conforms design partOf := by conforms

/-! ## The rules the design is for -/

/-- A module of part `p` never reaches, through any chain of LeanAPI's
    imports, a module of part `q`. -/
def NeverReaches (p q : Part) : Prop :=
  ∀ m m', imports.Reaches m m' → partOf m = some p → partOf m' ≠ some q

theorem neverReaches_of {p q : Part} (h : ¬ design.Reaches p q) : NeverReaches p q :=
  fun _ _ hr hp hq => h (conforms.reaches hr hp hq)

/-- **The property library knows nothing of sockets, threads or
    databases.** Its theorems are about plain functions. -/
theorem props_never_reach_the_server : NeverReaches props server ∧ NeverReaches props transport ∧
    NeverReaches props workers ∧ NeverReaches props leandb :=
  ⟨neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide))⟩

/-- **Typed endpoints, where `Api.step_safe`, `Api.inductive_of` and
    `Api.noninterference` live, do not reach the transport.** What those
    theorems are about is the code that runs; the server only carries bytes
    to it. -/
theorem endpoints_never_reach_the_transport :
    NeverReaches endpoints server ∧ NeverReaches endpoints transport :=
  ⟨neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide))⟩

/-- **Nor do database endpoints**: `DbApi.prog_denote` too is about code
    with no sockets in it. -/
theorem database_never_reaches_the_transport :
    NeverReaches database server ∧ NeverReaches database transport :=
  ⟨neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide))⟩

/-- **LeanDB is optional**: an HTTP-only application built from typed
    endpoints does not reach it. -/
theorem endpoints_never_reach_leandb : NeverReaches endpoints leandb :=
  neverReaches_of (Graph.not_reaches_of_check (by decide))

/-- **The actor depends on nothing**, so business rules can take one
    without depending on HTTP (`Architecture.Apps`). -/
theorem actor_is_a_leaf : NeverReaches actor wire ∧ NeverReaches actor transport :=
  ⟨neverReaches_of (Graph.not_reaches_of_check (by decide)),
   neverReaches_of (Graph.not_reaches_of_check (by decide))⟩

/-- **`Runtime/Server.lean` is the only module that imports `Std.Http`**, as
    its header says. `Std.Http` can change between toolchains; this keeps
    the change in one file. -/
theorem only_the_server_imports_std_http :
    ∀ e ∈ imports.edges, e.2 = `Std.Http → e.1 = `LeanApi.Runtime.Server := by
  decide +kernel

end Architecture.Framework
