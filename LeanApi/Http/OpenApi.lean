/-
  OpenAPI 3.1 generation from route metadata (M7), plus a proved-route
  coverage report.

  A `Route` can carry a `RouteDoc`: summary, parameters, request body and
  responses. Path parameters come from the template (`{id:int}` →
  integer). `Router.openApi` produces the document and `docsRoutes` serves
  it at `/openapi.json` with a minimal HTML page at `/docs`.

  Coverage (Q1/Q11 escape-hatch policy): a route is marked `proved` when it
  belongs to a proved operation table. `coverageReport` lists routes outside
  the proved set; `requireCoverage` fails the build/test when an unproved
  route is not explicitly allowed.
-/
import LeanApi.Http.Router
import Lean.Data.Json

namespace LeanApi

open Lean

structure ParamDoc where
  name : String
  location : String := "query"
  required : Bool := false
  schema : Json := Json.mkObj [("type", .str "string")]
  description : String := ""

structure RouteDoc where
  summary : String := ""
  params : List ParamDoc := []
  requestBody : Option Json := none
  responses : List (Nat × String) := [(200, "OK")]
  security : Bool := false
  /-- Belongs to a proved operation table (EVIDENCE.md). -/
  proved : Bool := false

/-- Route documentation registry, kept beside the route list (routes stay
    plain data; docs are keyed by method and template). -/
abbrev Docs := List ((Method × String) × RouteDoc)

private def segSchema : ParamKind → Json
  | .any => Json.mkObj [("type", .str "string")]
  | .int => Json.mkObj [("type", .str "integer")]
  | .nat => Json.mkObj [("type", .str "integer"), ("minimum", Json.num 0)]

private def openApiPath (segs : List Seg) : String :=
  "/" ++ "/".intercalate (segs.map fun
    | .lit s => s
    | .param n _ => "{" ++ n ++ "}"
    | .rest n => "{" ++ n ++ "}")

private def problemResponse (desc : String) : Json :=
  Json.mkObj [("description", .str desc),
    ("content", Json.mkObj [("application/problem+json", Json.mkObj [("schema", Json.mkObj [("$ref", .str "#/components/schemas/Problem")])])])]

def Router.openApi (r : Router) (docs : Docs) (title : String) (version : String) : Json :=
  let byPath : List (String × List (String × Json)) :=
    r.routes.toList.foldl (init := []) fun acc c =>
      let path := openApiPath c.segs
      let doc := (docs.lookup (c.route.method, c.route.template)).getD {}
      let pathParams := c.segs.filterMap fun
        | .param n k => some (Json.mkObj [("name", .str n), ("in", .str "path"), ("required", .bool true), ("schema", segSchema k)])
        | .rest n => some (Json.mkObj [("name", .str n), ("in", .str "path"), ("required", .bool true), ("schema", segSchema .any)])
        | .lit _ => none
      let extra := doc.params.map fun p =>
        Json.mkObj ([("name", .str p.name), ("in", .str p.location), ("required", .bool p.required), ("schema", p.schema)] ++
          (if p.description.isEmpty then [] else [("description", .str p.description)]))
      let responses := Json.mkObj (doc.responses.map fun (code, d) =>
        (toString code, if code ≥ 400 then problemResponse d else Json.mkObj [("description", .str d)]))
      let op := Json.mkObj ([
          ("operationId", .str (c.route.name.getD s!"{c.route.method}{c.route.template}")),
          ("summary", .str doc.summary),
          ("parameters", Json.arr (pathParams ++ extra).toArray),
          ("responses", responses),
          ("x-leanapi-proved", .bool doc.proved)] ++
        (match doc.requestBody with
          | some schema => [("requestBody", Json.mkObj [("required", .bool true),
              ("content", Json.mkObj [("application/json", Json.mkObj [("schema", schema)])])])]
          | none => []) ++
        (if doc.security then [("security", Json.arr #[Json.mkObj [("bearer", Json.arr #[])]])] else []))
      let m := (toString c.route.method).toLower
      match acc.lookup path with
      | some ops => (acc.filter (·.1 != path)) ++ [(path, ops ++ [(m, op)])]
      | none => acc ++ [(path, [(m, op)])]
  Json.mkObj [
    ("openapi", .str "3.1.0"),
    ("info", Json.mkObj [("title", .str title), ("version", .str version)]),
    ("paths", Json.mkObj (byPath.map fun (p, ops) => (p, Json.mkObj ops))),
    ("components", Json.mkObj [
      ("securitySchemes", Json.mkObj [("bearer", Json.mkObj [("type", .str "http"), ("scheme", .str "bearer")])]),
      ("schemas", Json.mkObj [("Problem", Json.mkObj [("type", .str "object"),
        ("properties", Json.mkObj [("type", Json.mkObj [("type", .str "string")]),
          ("title", Json.mkObj [("type", .str "string")]), ("status", Json.mkObj [("type", .str "integer")]),
          ("detail", Json.mkObj [("type", .str "string")])])])])])]

/-- `GET /openapi.json` and `GET /docs` (a page that loads the spec). -/
def docsRoutes (spec : Json) (title : String := "API") : List Route := [
  Route.get "/openapi.json" fun _ => pure (Res.json spec),
  Route.get "/docs" fun _ => pure (Res.html s!"<!doctype html><html><head><meta charset=\"utf-8\"><title>{title}</title></head>
<body><h1>{title}</h1><p>OpenAPI document: <a href=\"/openapi.json\">/openapi.json</a></p>
<pre id=\"spec\"></pre><script>fetch('/openapi.json').then(r=>r.json()).then(j=>document.getElementById('spec').textContent=JSON.stringify(j,null,2))</script>
</body></html>")]

/-! ## Coverage -/

structure Coverage where
  proved : List String
  unproved : List String

def Router.coverage (r : Router) (docs : Docs) : Coverage :=
  let label (c : CompiledRoute) := s!"{c.route.method} {renderTemplate c.segs}"
  let isProved (c : CompiledRoute) := ((docs.lookup (c.route.method, c.route.template)).map (·.proved)).getD false
  { proved := (r.routes.toList.filter isProved).map label
    unproved := (r.routes.toList.filter (!isProved ·)).map label }

def Coverage.report (c : Coverage) : String :=
  s!"proved routes ({c.proved.length}):\n" ++ String.join (c.proved.map (s!"  ✓ {·}\n")) ++
  s!"routes outside the proved set ({c.unproved.length}):\n" ++ String.join (c.unproved.map (s!"  · {·}\n"))

/-- Routes outside the proved set that are not in `allowed`. Empty means
    coverage matches what EVIDENCE.md declares. -/
def Coverage.undeclared (c : Coverage) (allowed : List String) : List String :=
  c.unproved.filter (!allowed.contains ·)

end LeanApi
