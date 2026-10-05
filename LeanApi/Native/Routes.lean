import LeanApi.Native.Contract
import LeanApi.Core.Flow

/-! Explicit routes over generated operations. `route_binding% post "/orders/:order/items" op`
is a checked `RouteBinding`: every `:name` segment must name a field of the operation's
input record, that field's type must have a `PathParam` codec, and `get` accepts only a
query operation whose inputs all come from the path. Each failure is an elaboration error
naming the parameter (or field) and the operation. -/
namespace LeanApi.Native
open Lean Ontology

/-- How one URL path segment becomes a typed value. Identifiers and plain scalars have
one; `Password` and `Email` deliberately do not, so they never appear in a URL. -/
class PathParam (T : Type) where
  parse : String → Validation T

instance [HasTypeId T] : PathParam (Ontology.Ref T) := ⟨fun segment => Ontology.Ref.parse segment⟩

instance : PathParam Nat where
  parse segment := match JsonWire.decimalInt? segment with
    | some value => if value ≥ 0 && toString value == segment then .ok value.toNat
      else Validation.fail "path.noncanonical_natural"
    | none => Validation.fail "path.invalid_natural"

instance : PathParam Int where
  parse segment := match JsonWire.decimalInt? segment with
    | some value => if toString value == segment then .ok value else Validation.fail "path.noncanonical_integer"
    | none => Validation.fail "path.invalid_integer"

instance : PathParam String where
  parse segment := if segment.isEmpty then Validation.fail "path.empty_segment" else .ok segment

instance : PathParam Ontology.Name := ⟨Ontology.Name.parse⟩
instance : PathParam Ontology.Title := ⟨Ontology.Title.parse⟩
instance : PathParam Ontology.Instant := ⟨Ontology.Instant.parse⟩

/-- The segment decoder of one path field: the typed path codec, then the same canonical
`Wire` encoding the operation's input record codec uses for that field. -/
def PathField.of (name : String) (T : Type) [PathParam T] [Wire T] : PathField :=
  { name, decode := fun segment => (Wire.codec (α := T)).encode <$> PathParam.parse segment }

open Meta Elab Term

/-- A checked path parameter: the input field it binds and that field's type. -/
structure RouteField where
  name : String
  type : Expr

/-- The input record fields of a generated operation, with their types. A non-record
input (`Unit`) has none. -/
def operationInputFields (operation : Lean.Name) : MetaM (Array (String × Expr)) := do
  let type ← instantiateMVars (← getConstInfo operation).type
  unless type.isAppOfArity ``LeanApi.Core.Operation 5 do
    throwError "{operation} is not a domain operation (LeanApi.Core.Operation)"
  let input ← whnf (type.getArg! 2)
  let env ← getEnv
  let .const structName _ := input.getAppFn | return #[]
  unless isStructure env structName do return #[]
  (getStructureFields env structName).mapM fun field => do
    let projection ← getConstInfo (structName ++ field)
    let fieldType ← forallTelescopeReducing projection.type fun _ body => pure body
    if fieldType.hasFVar || fieldType.hasLooseBVars then
      throwError "{operation}: dependent input field {field} cannot be bound from a path"
    return (field.toString, fieldType)

/-- Elaboration-time route check, shared by `route_binding%` and `app% … routes := […]`. -/
def checkRoute (method template : String) (operation : Lean.Name) : MetaM (Array RouteField) := do
  unless method == "get" || method == "post" do
    throwError "route method must be get or post, not {method}"
  let segments ← match parseRouteTemplate template with
    | .ok segments => pure segments
    | .error message => throwError "route {method} \"{template}\": {message}"
  let type ← instantiateMVars (← getConstInfo operation).type
  unless type.isAppOfArity ``LeanApi.Core.Operation 5 do
    throwError "route {method} \"{template}\": {operation} is not a domain operation"
  let kind ← whnf (type.getArg! 0)
  let fields ← operationInputFields operation
  let names := segments.filterMap fun | .param name => some name | _ => none
  let fieldList := if fields.isEmpty then "it has no input fields"
    else "its input fields are " ++ ", ".intercalate (fields.toList.map Prod.fst)
  let mut bound := #[]
  for name in names do
    let some (_, fieldType) := fields.find? (·.1 == name)
      | throwError "path parameter :{name} in \"{template}\" has no matching input field in {operation}; {fieldList}"
    if (← synthInstance? (← mkAppM ``PathParam #[fieldType])).isNone then
      throwError "path parameter :{name} in \"{template}\" binds {operation} input field {name} : {fieldType}, which has no LeanApi.Native.PathParam instance"
    if (← synthInstance? (← mkAppM ``Ontology.Wire #[fieldType])).isNone then
      throwError "path parameter :{name} in \"{template}\" binds {operation} input field {name} : {fieldType}, which has no Wire instance"
    bound := bound.push ⟨name, fieldType⟩
  if method == "get" then
    unless kind.isConstOf ``Contract.OperationKind.query do
      throwError "GET \"{template}\" requires a query operation, but {operation} is a command; publish it with post"
    for (field, _) in fields do
      unless names.contains field do
        throwError "GET \"{template}\": input field {field} of {operation} is not bound by a path parameter; a GET route reads every input from its path"
  return bound

/-- The checked binding as a term. Body format is plain: the input record itself, path fields from the path. -/
def routeBindingExpr (method template : String) (fields : Array RouteField) : MetaM Expr := do
  let fieldExprs ← fields.mapM fun field =>
    mkAppOptM ``PathField.of #[some (toExpr field.name), some field.type, none, none]
  let list ← mkListLit (Lean.mkConst ``PathField) fieldExprs.toList
  let methodExpr := Lean.mkConst (if method == "get" then ``LeanApi.Method.get else ``LeanApi.Method.post)
  return mkAppN (Lean.mkConst ``RouteBinding.mk)
    #[methodExpr, toExpr template, list, Lean.mkConst ``BodyFormat.plain, toExpr (some 16384 : Option Nat)]

syntax (name := routeBindingTerm) "route_binding% " ident str ident : term

@[term_elab routeBindingTerm]
def elabRouteBinding : TermElab := fun stx _ => do
  let method := stx[1].getId.toString
  let some template := stx[2].isStrLit? | throwErrorAt stx[2] "expected a path template"
  let operation ← realizeGlobalConstNoOverloadWithInfo stx[3]
  let fields ← checkRoute method template operation
  routeBindingExpr method template fields

end LeanApi.Native
