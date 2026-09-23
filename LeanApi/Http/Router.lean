/-
  Routing.

  Templates: `/games/{id}`, `/games/{id:int}`, `/files/{*path}`.
  * A literal matches one decoded segment exactly.
  * `{name}` matches one nonempty segment; `{name:int}` / `{name:nat}` only
    segments that parse as such.
  * `{*name}` matches the (possibly empty) rest of the path, joined by `/`.
    It must be last.

  Precedence, segment by segment from the left: literal, then constrained
  parameter, then plain parameter, then catch-all. The first segment where
  two candidate routes differ decides, so `/games/new` beats
  `/games/{id}` for `GET /games/new`, independent of declaration order.

  Two routes conflict when they have the same method and the same shape
  (same literals and parameter kinds, names ignored). `Router.build`
  rejects conflicts, malformed templates and a catch-all that is not last.
  `routes!` runs the same check while elaborating, so a conflict is a
  compile error.

  Resolution:
  * `..` or `.` segments are refused with 400 before matching (no
    normalization, so no traversal through templates).
  * Path matches but no route for the method: 405 with `Allow`.
  * `HEAD` without its own route runs the `GET` route; the transport drops
    the body.
  * `OPTIONS` without its own route: 204 with `Allow`.
  * Trailing slash: policy `redirect` (default) answers `GET`/`HEAD` with a
    308 to the path without the slash when that path has a route, and 404
    otherwise; `strict` treats `/a/` as not found; `ignore` routes it as `/a`.
-/
import LeanApi.Http.Request
import Lean

namespace LeanApi

inductive ParamKind where
  | any | int | nat
  deriving Repr, DecidableEq, BEq, Inhabited

def ParamKind.accepts : ParamKind → String → Bool
  | .any, s => !s.isEmpty
  | .int, s => s.toInt?.isSome && !s.isEmpty
  | .nat, s => s.toNat?.isSome

inductive Seg where
  | lit (s : String)
  | param (name : String) (kind : ParamKind)
  | rest (name : String)
  deriving Repr, DecidableEq, BEq, Inhabited

/-- Precedence rank of a segment: lower wins. -/
def Seg.rank : Seg → Nat
  | .lit _ => 0
  | .param _ .any => 2
  | .param _ _ => 1
  | .rest _ => 3

/-- The segment with names erased, for conflict detection. -/
def Seg.shape : Seg → Seg
  | .lit s => .lit s
  | .param _ k => .param "" k
  | .rest _ => .rest ""

def Seg.render : Seg → String
  | .lit s => s
  | .param n .any => "{" ++ n ++ "}"
  | .param n .int => "{" ++ n ++ ":int}"
  | .param n .nat => "{" ++ n ++ ":nat}"
  | .rest n => "{*" ++ n ++ "}"

def parseSeg (s : String) : Except String Seg :=
  if s.startsWith "{" && s.endsWith "}" then
    let inner := ((s.drop 1).dropEnd 1).toString
    if inner.startsWith "*" then
      let n := (inner.drop 1).toString
      if n.isEmpty then .error s!"catch-all needs a name: {s}" else .ok (.rest n)
    else match inner.splitOn ":" with
      | [n] => if n.isEmpty then .error s!"empty parameter name: {s}" else .ok (.param n .any)
      | [n, "int"] => .ok (.param n .int)
      | [n, "nat"] => .ok (.param n .nat)
      | _ => .error s!"unknown parameter form: {s}"
  else if s.contains '{' || s.contains '}' then .error s!"braces inside a literal segment: {s}"
  else .ok (.lit s)

/-- Parse a template. `/` is the empty pattern. -/
def parseTemplate (t : String) : Except String (List Seg) := do
  unless t.startsWith "/" do throw s!"template must start with '/': {t}"
  let raw := (t.splitOn "/").drop 1
  let raw := if raw == [""] then [] else raw
  if raw.any (·.isEmpty) then throw s!"empty segment in template: {t}"
  let segs ← raw.mapM parseSeg
  let n := segs.length
  for i in [0:n] do
    match segs[i]? with
    | some (.rest _) => if i + 1 != n then throw s!"catch-all must be the last segment: {t}"
    | _ => pure ()
  let names := segs.filterMap fun | .param n _ => some n | .rest n => some n | _ => none
  if names.eraseDups.length != names.length then throw s!"duplicate parameter name in {t}"
  return segs

def renderTemplate (segs : List Seg) : String := "/" ++ "/".intercalate (segs.map Seg.render)

/-- Match decoded segments against a pattern, returning parameters. -/
def matchSegs : List Seg → List String → Option (List (String × String))
  | [], [] => some []
  | [.rest n], xs => some [(n, "/".intercalate xs)]
  | .lit l :: ps, x :: xs => if l == x then matchSegs ps xs else none
  | .param n k :: ps, x :: xs =>
      if k.accepts x then (matchSegs ps xs).map ((n, x) :: ·) else none
  | _, _ => none

/-- Compare two patterns by precedence (lexicographic on segment rank). -/
def morePrecise : List Seg → List Seg → Bool
  | a :: as, b :: bs => if a.rank < b.rank then true else if b.rank < a.rank then false else morePrecise as bs
  | [], _ :: _ => true
  | _, _ => false

/-- A route before building: pure metadata plus a handler. -/
structure Route where
  method : Method
  template : String
  handler : App
  /-- Request body limit in bytes, enforced while reading. -/
  bodyLimit : Nat := 1024 * 1024
  /-- A name for logs and API descriptions. -/
  name : Option String := none
  /-- Free-form tags (documentation, OpenAPI). -/
  tags : List String := []

instance : Inhabited Route := ⟨{ method := .get, template := "/", handler := fun _ => pure {} }⟩

namespace Route
def get (t : String) (h : App) : Route := { method := .get, template := t, handler := h }
def post (t : String) (h : App) : Route := { method := .post, template := t, handler := h }
def put (t : String) (h : App) : Route := { method := .put, template := t, handler := h }
def patch (t : String) (h : App) : Route := { method := .patch, template := t, handler := h }
def delete (t : String) (h : App) : Route := { method := .delete, template := t, handler := h }
def head (t : String) (h : App) : Route := { method := .head, template := t, handler := h }
def options (t : String) (h : App) : Route := { method := .options, template := t, handler := h }

def limit (r : Route) (n : Nat) : Route := { r with bodyLimit := n }
def named (r : Route) (n : String) : Route := { r with name := some n }
def wrap (r : Route) (mw : App → App) : Route := { r with handler := mw r.handler }
end Route

/-- Prefix every route with `pre` (e.g. `"/api/v1"`) and wrap each handler
    in `mw` (group middleware, applied inside global middleware). -/
def group (pre : String) (rs : List Route) (mw : App → App := id) : List Route :=
  let pre := if pre.endsWith "/" then (pre.dropEnd 1).toString else pre
  rs.map fun r =>
    { r with template := if r.template == "/" then (if pre.isEmpty then "/" else pre) else pre ++ r.template
             handler := mw r.handler }

/-- Why a route list does not build. Only depends on methods and templates,
    so it can be decided at elaboration time. -/
def routeErrors (rs : List (Method × String)) : List String :=
  let parsed := rs.map fun (m, t) => (m, t, parseTemplate t)
  let bad := parsed.filterMap fun (_, _, r) => match r with | .error e => some e | .ok _ => none
  let good := parsed.filterMap fun (m, t, r) => match r with | .ok s => some (m, t, s.map Seg.shape) | .error _ => none
  let rec dups : List (Method × String × List Seg) → List String
    | [] => []
    | (m, t, s) :: rest =>
        (rest.filterMap fun (m', t', s') =>
          if m == m' && s == s' then some s!"{m} {t} conflicts with {m'} {t'}" else none) ++ dups rest
  bad ++ dups good

inductive TrailingSlash where
  | redirect | strict | ignore
  deriving Repr, BEq, Inhabited

structure CompiledRoute where
  route : Route
  segs : List Seg

instance : Inhabited CompiledRoute := ⟨⟨default, []⟩⟩

structure Router where
  routes : Array CompiledRoute
  trailingSlash : TrailingSlash := .redirect
  /-- Response for unmatched paths. -/
  notFound : App := fun _ => pure Problem.notFound.toRes

instance : Inhabited Router := ⟨{ routes := #[] }⟩

namespace Router

def build (rs : List Route) (trailingSlash : TrailingSlash := .redirect) : Except String Router := do
  match routeErrors (rs.map fun r => (r.method, r.template)) with
  | [] => pure ()
  | es => throw ("invalid routes:\n  " ++ "\n  ".intercalate es)
  let compiled ← rs.mapM fun r => do return { route := r, segs := ← parseTemplate r.template : CompiledRoute }
  return { routes := compiled.toArray, trailingSlash }

/-- Build, panicking on invalid routes. For programs whose route table is
    fixed; use `routes!` to move the check to compile time. -/
def build! (rs : List Route) (trailingSlash : TrailingSlash := .redirect) : Router :=
  match build rs trailingSlash with
  | .ok r => r
  | .error e => panic! e

/-- What resolution decided for a request head: a table entry and its
    path parameters, or a response (400, 404, 405, 308, OPTIONS 204). -/
inductive Resolution (ρ : Type) where
  | route (r : ρ) (params : List (String × String))
  | respond (res : Res)

instance : Inhabited (Resolution ρ) := ⟨.respond {}⟩

/-- Entries whose pattern matches the path, most precise first. -/
def candidatesIn (entries : List (ρ × Method × List Seg)) (path : List String) :
    List ((ρ × Method × List Seg) × List (String × String)) :=
  let ms := entries.filterMap fun e => (matchSegs e.2.2 path).map (e, ·)
  ms.mergeSort fun a b => morePrecise a.1.2.2 b.1.2.2 || a.1.2.2 == b.1.2.2

def methodsIn (entries : List (ρ × Method × List Seg)) (path : List String) : List Method :=
  let ms := (candidatesIn entries path).map (·.1.2.1)
  let ms := if ms.contains .get && !ms.contains .head then ms ++ [.head] else ms
  let ms := if ms.contains .options then ms else ms ++ [.options]
  Method.all.filter ms.contains

private def allowHeader (ms : List Method) : String := ", ".intercalate (ms.map toString)

/-- Route resolution over any table of `(entry, method, pattern)`. Pure and
    independent of the body. The native `Router` and the reference model of
    proved routes (`LeanApi.Operation`) both resolve through this function. -/
def resolveIn (entries : List (ρ × Method × List Seg)) (ts : TrailingSlash) (req : Req) : Resolution ρ :=
  if req.path.any (fun s => s == "." || s == "..") then
    .respond (Problem.badRequest "dot segments are not allowed in paths").toRes
  else
  if req.trailingSlash && ts != .ignore then
    if ts == .redirect && (req.method == .get || req.method == .head)
        && !(candidatesIn entries req.path).isEmpty then
      let q := if req.query.isEmpty then "" else
        "?" ++ "&".intercalate (req.query.map fun (k, v) => Url.percentEncode k ++ "=" ++ Url.percentEncode v)
      .respond (Res.redirect ({ req with trailingSlash := false }.pathString ++ q) 308)
    else .respond Problem.notFound.toRes
  else
  let cs := candidatesIn entries req.path
  if cs.isEmpty then .respond Problem.notFound.toRes else
  match cs.find? (·.1.2.1 == req.method) with
  | some (e, ps) => .route e.1 ps
  | none =>
    match req.method, cs.find? (·.1.2.1 == .get) with
    | .head, some (e, ps) => .route e.1 ps
    | .options, _ =>
        .respond ((Res.empty 204).setHeader "allow" (allowHeader (methodsIn entries req.path)))
    | _, _ =>
        .respond ((Problem.make 405).withHeader "allow" (allowHeader (methodsIn entries req.path))).toRes

def entries (r : Router) : List (CompiledRoute × Method × List Seg) :=
  r.routes.toList.map fun c => (c, c.route.method, c.segs)

def candidates (r : Router) (path : List String) : List (CompiledRoute × List (String × String)) :=
  (candidatesIn r.entries path).map fun (e, ps) => (e.1, ps)

def methodsFor (r : Router) (path : List String) : List Method := methodsIn r.entries path

def resolve (r : Router) (req : Req) : Resolution CompiledRoute := resolveIn r.entries r.trailingSlash req

/-- Body limit for the request's route (the edge reads at most this much).
    `none` for unrouted requests: their body is never read, and the router
    answers (404, 405, redirect) without it. -/
def bodyLimit (r : Router) (req : Req) : Option Nat :=
  match r.resolve req with
  | .route c _ => some c.route.bodyLimit
  | .respond _ => none

/-- Run the router as an app. -/
def app (r : Router) : App := fun req =>
  match r.resolve req with
  | .route c ps => c.route.handler { req with params := ps }
  | .respond res => if res.status == 404 then r.notFound req else pure res

/-- The route table as text, sorted by template, for inspection. -/
def describe (r : Router) : String :=
  let lines := r.routes.toList.map fun c =>
    s!"{c.route.method} {renderTemplate c.segs}" ++
      (match c.route.name with | some n => s!"  ({n})" | none => "") ++
      s!"  limit={c.route.bodyLimit}"
  "\n".intercalate (lines.mergeSort (· ≤ ·))

end Router

/-! ## Compile-time route checking -/

open Lean Elab Term Meta in
/-- `routes! [r1, r2, ...]` elaborates the list and, for each route,
    reduces only its method and template (never its handler, so handlers
    may close over local variables). A conflict or malformed template is an
    elaboration error. The result is the `List Route` itself. -/
elab "routes!" xs:term : term => do
  let e ← elabTerm xs (some (mkApp (mkConst ``List [0]) (mkConst ``LeanApi.Route)))
  let e ← instantiateMVars e
  let mut rs : Array Expr := #[]
  let mut l ← whnfR e
  repeat
    match l.getAppFnArgs with
    | (``List.cons, #[_, h, t]) => rs := rs.push h; l ← whnfR t
    | (``List.nil, _) => break
    | _ => throwError "routes!: expected a list literal"
  let mut keys : List (Method × String) := []
  for r in rs do
    let m ← reduce (← mkAppM ``LeanApi.Route.method #[r])
    let t ← reduce (← mkAppM ``LeanApi.Route.template #[r])
    if m.hasFVar || t.hasFVar || m.hasMVar || t.hasMVar then
      throwErrorAt xs "routes!: could not compute a route's method and template statically"
    let mv ← unsafe evalExpr Method (mkConst ``LeanApi.Method) m
    let tv ← unsafe evalExpr String (mkConst ``String) t
    keys := keys ++ [(mv, tv)]
  let errs := routeErrors keys
  unless errs.isEmpty do
    throwError m!"invalid routes:\n  {"\n  ".intercalate errs}"
  return e

end LeanApi
