import LeanApi.Core.Auth

/-! # Publishing a plain operation (contract derivation)

`derive_operation f` (also run by an `Api` declaration for each listed function) reads the
operation contract off the type of an ordinary `def`:

```
def borrow (me : Signed) (book : Ref Book) : Op BorrowError (Ref Loan) := …
```

* the parameter whose type is a `Principal` (or `Option` of one) is the actor, never input;
* every other explicit parameter becomes a field of the generated `borrow.Input` record;
* `Op ε α` publishes a command, `ReadOp ε α` a query; `ε` is the closed error, `α` the output.

It generates, next to `f` (all are ordinary declarations you can `#check`):

```
f.Input                 : Type                       -- record of the non-actor arguments
f.Requirements          : Resources → Type 1         -- typed capabilities f's body uses
f.Requirements.infer    : [capabilities…] → f.Requirements resources
f.portableRequirements  : f.Requirements portableResources
f.flowWithResources     : {resources} → f.Requirements resources → {Scope} → (args…) →
                          Flow kind Scope ε α resources
f.Actor                 : Type → Type                -- `fun Scope => SignedIn` (or `Unit`)
f.bodyWithResources     : {resources} → f.Requirements resources → {Scope} → f.Actor Scope →
                          f.Input → Flow kind Scope ε α resources
f.operation             : Operation kind f.Actor f.Input α ε
instance : PublishedOperation f kind f.Actor f.Input α ε     -- so `post "/x" f` finds it
```

`f.flowWithResources` is `f`'s OWN elaborated body, generalized by LeanDB's requirements
machinery (`LeanDb.Model.Requirements.generalize`) with this layer's targets: the operation
family `portableResources`, LeanDB's `portableStorage` as its storage part, LeanDB's named
portable instances and `portableAuth`. The kernel re-checks the result. Requirements are
exactly the typed capabilities the body's storage and auth calls demanded.

Limitations (reported as errors): `partial`/opaque helpers, implicit/instance parameters, and
argument types that depend on other arguments cannot be published. -/

namespace LeanApi.Core.Publish
open Lean Meta Elab Command LeanDb.Model

/-- What publication abstracts: the operation family, with LeanDB's storage family as its
`toStorageResources`, and the named portable instances of both layers. -/
def targets : Requirements.Targets where
  familyType := mkConst ``Resources
  portable := ``portableResources
  derived := #[(``portableStorage, fun family => mkApp (mkConst ``Resources.toStorageResources) family)]
  instances := Requirements.portableInstances.push ``portableAuth

/-- One step of the unfolded body, for `f.operation.metadata.nodes`. -/
structure Node where
  kind : String
  effect : Contract.OperationKind
  detail : String
  failure : Option String := none
  constraints : List String := []

private def operationRequests : List (Lean.Name × Contract.OperationKind) :=
  [(``RequestF.now, .query), (``RequestF.hashPassword, .command), (``RequestF.verifyCredential, .command),
   (``RequestF.startSession, .command)]

/-- The entity argument (`T`) of an operation-level request, if any. -/
private def requestEntity (c : Lean.Name) (args : Array Expr) : MetaM String := do
  forallTelescope (← getConstInfo c).type fun binders _ => do
    let names ← binders.mapM fun b => return (← b.fvarId!.getDecl).userName
    match names.findIdx? (· == `T) >>= (args[·]?) with
    | some (.const t _) => return t.toString
    | _ => return ""

/-- Ordered storage steps, operation requests and guards of the unfolded body. -/
partial def scanNodes (e : Expr) : MetaM (Array Node) := do
  let out ← IO.mkRef (#[] : Array Node)
  let failureOf (err : Expr) : MetaM (Option String) := do
    match err.getAppFn with
    | .const c _ => if err.getAppNumArgs == 0 then return some c.getString! else return none
    | _ => return none
  let seen ← IO.mkRef (Std.HashSet.emptyWithCapacity 64 : Std.HashSet Expr)
  let rec visit (e : Expr) : MetaM Unit := do
    if (← seen.get).contains e then return
    seen.modify (·.insert e)
    match e with
    | .app .. =>
      let fn := e.getAppFn
      let args := e.getAppArgs
      if let some node ← Requirements.storageNode? e then
        let effect : Contract.OperationKind := match node.access with
          | .command => .command
          | .query => .query
        out.modify (·.push { kind := node.kind, effect, detail := node.entity, constraints := node.constraints })
      else if let .const c _ := fn then
        if let some (_, effect) := operationRequests.find? (·.1 == c) then
          let detail ← requestEntity c args
          out.modify (·.push { kind := c.getString!, effect, detail })
        else if (c == ``FlowF.check || c == ``Flow.check || c == ``MonadRequire.requireWith) && args.size >= 6 &&
            !args.back!.hasLooseBVars then
          out.modify (·.push { kind := "require", effect := .query, detail := "", failure := ← failureOf args.back! })
        else if (c == ``FlowF.fail || c == ``Flow.fail || c == ``MonadExcept.throw || c == ``MonadExceptOf.throw) &&
            args.size ≥ 4 && !args.back!.hasLooseBVars then
          out.modify (·.push { kind := "throw", effect := .query, detail := "", failure := ← failureOf args.back! })
      visit fn
      for arg in args do visit arg
    | .lam _ _ b _ => visit b
    | .forallE .. => pure ()
    | .letE _ _ v b _ => visit v; visit b
    | .mdata _ b => visit b
    | .proj _ _ b => visit b
    | _ => pure ()
  visit e
  out.get

/-- KDF steps the body can reach, keyed by the input field each consumes (decision 4). A KDF
input that is not one of the operation's own (non-actor) arguments cannot be prepared before
writer admission, so it is a publication error. -/
def kdfSteps (f : Lean.Name) (params : Array Lean.Name) (actors : Array Bool) (inlined : Expr) : MetaM (List KdfStep) :=
  lambdaTelescope inlined fun binders body => do
    let steps ← IO.mkRef (#[] : Array KdfStep)
    let mut failure : Option String := none
    let check (kind : String) (password : Expr) : MetaM (Option String) := do
      match binders.findIdx? (· == password) with
      | some i =>
        if i < params.size then
          if actors[i]! then return some s!"its {kind} input is the actor"
          return none
        else return some s!"its {kind} input is not an argument of `{f}`"
      | none => return some s!"`{kind}` must be applied directly to a `Password` argument of `{f}`"
    let found ← IO.mkRef (#[] : Array (String × Expr))
    body.forEach fun e => do
      if e.isAppOfArity ``RequestF.hashPassword 3 then found.modify (·.push ("Password.hash", e.appArg!))
      if e.isAppOfArity ``RequestF.verifyCredential 10 then found.modify (·.push ("Credential.verify", e.appArg!))
    for (kind, password) in ← found.get do
      if let some problem ← check kind password then
        failure := some problem
      else
        let i := (binders.findIdx? (· == password)).getD 0
        let field := params[i]!.toString
        let step := if kind == "Password.hash" then KdfStep.hash field else KdfStep.verify field
        unless (← steps.get).contains step do steps.modify (·.push step)
    if let some problem := failure then
      throwError "cannot publish `{f}`: {problem}, so the runtime cannot run the KDF before writer admission"
    return (← steps.get).toList

/-- A parameter of a published function. -/
structure Parameter where
  name : Lean.Name
  type : Expr
  actor : Bool
  deriving Inhabited

/-- Is `type` an actor (a `Principal` instance, or `Option` of one)? -/
def isActorType (type : Expr) : MetaM Bool := do
  let candidate := if type.isAppOfArity ``Option 1 then type.appArg! else type
  return (← synthInstance? (mkApp (mkConst ``Principal) candidate)).isSome

/-- Shape of a published function: parameters, kind, error and output. -/
structure Shape where
  params : Array Parameter
  kind : Contract.OperationKind
  error : Expr
  output : Expr

def shapeOf (f : Lean.Name) : MetaM Shape := do
  let info ← getConstInfo f
  unless info.levelParams.isEmpty do throwError "cannot publish `{f}`: universe-polymorphic operations are not supported"
  forallTelescope info.type fun args result => do
    let (kind, error, output) ← match result.getAppFn, result.getAppArgs with
      | .const ``LeanApi.Core.Op _, #[ε, α] => pure (Contract.OperationKind.command, ε, α)
      | .const ``LeanApi.Core.ReadOp _, #[ε, α] => pure (Contract.OperationKind.query, ε, α)
      | _, _ => throwError "cannot publish `{f}`: its result type{indentExpr result}\nmust be `Op ε α` (read-write) or `ReadOp ε α` (read-only)"
    let mut params := #[]
    let mut actors := 0
    for arg in args do
      let decl ← arg.fvarId!.getDecl
      unless decl.binderInfo.isExplicit do
        throwError "cannot publish `{f}`: parameter `{decl.userName}` must be explicit"
      if decl.type.hasAnyFVar (fun fvar => args.contains (.fvar fvar)) then
        throwError "cannot publish `{f}`: the type of parameter `{decl.userName}` depends on another parameter"
      let actor ← isActorType decl.type
      if actor then actors := actors + 1
      if actors > 1 then throwError "cannot publish `{f}`: at most one actor (`SignedIn`/`Option SignedIn`) parameter is supported"
      params := params.push { name := decl.userName.eraseMacroScopes, type := decl.type, actor }
    if error.hasAnyFVar (fun fvar => args.contains (.fvar fvar)) || output.hasAnyFVar (fun fvar => args.contains (.fvar fvar)) then
      throwError "cannot publish `{f}`: the error and output types must not depend on the arguments"
    return { params, kind, error, output }

/-- Constructor names of a closed error type, in declaration order. -/
def failuresOf (error : Expr) : MetaM (List String) := do
  match error.getAppFn with
  | .const c _ =>
    match (← getEnv).find? c with
    | some (.inductInfo info) => return info.ctors.map (·.getString!)
    | _ => return []
  | _ => return []

private def kindSyntax : Contract.OperationKind → String
  | .command => "command"
  | .query => "query"

/-- Generate the `Operation` value and its input record for a published function. -/
def deriveOperation (f : Lean.Name) (ref : Syntax) : CommandElabM Unit := do
  if (← getEnv).contains (f ++ `operation) then return
  let shape ← liftTermElabM <| shapeOf f
  -- Wire codecs for authored value types (error, output, inputs) declared in this module.
  Deriving.ensureWire shape.error
  Deriving.ensureWire shape.output
  for param in shape.params do
    unless param.actor do Deriving.ensureWire param.type
  for (what, ty) in [("error", shape.error), ("output", shape.output)] ++
      (shape.params.filter (!·.actor)).toList.map (fun p => (s!"argument `{p.name}`", p.type)) do
    unless ← liftTermElabM (return (← synthInstance? (mkApp (mkConst ``Ontology.Wire) ty)).isSome) do
      throwErrorAt ref "cannot publish `{f}`: the {what} type {← liftTermElabM (ppExpr ty)} has no wire codec (entities, rows and actors are never published)"
  let inputs := shape.params.filter (!·.actor)
  let full := Deriving.full
  let inputName := f ++ `Input
  if inputs.isEmpty then
    Deriving.runCommand ("abbrev " ++ full inputName ++ " := Unit")
  else
    let fields ← liftTermElabM <| inputs.mapM (m := TermElabM) fun p => do
      return p.name.toString ++ " : " ++ (← Deriving.sourceOf p.type)
    Deriving.runCommand ("structure " ++ full inputName ++ " where\n  " ++ String.intercalate "\n  " fields.toList ++ "\n  deriving LeanDb.Model.Domain")
    if inputs.size == 1 && (← liftTermElabM (whnfR inputs[0]!.type)).isAppOfArity ``Ontology.EntityId 1 then
      let target ← liftTermElabM do Deriving.sourceOf (← whnfR inputs[0]!.type).appArg!
      Deriving.runCommand ("instance : LeanApi.Core.RouteInput " ++ full inputName ++ " := { Target := " ++ target ++
        ", targetIdentity := inferInstance, parse := fun raw => (Ontology.Ref.parse (T := " ++ target ++ ") raw).map " ++
        full inputName ++ ".mk, reference := " ++ full (inputName ++ inputs[0]!.name) ++ " }")
  let (nodes, kdf) ← liftTermElabM do
    let generalized ← Requirements.generalize targets f (f ++ `flowWithResources)
    let nodes ← scanNodes generalized.inlined
    let kdf ← kdfSteps f (shape.params.map (·.name)) (shape.params.map (·.actor)) generalized.inlined
    return (nodes, kdf)
  -- bodyWithResources {resources} requirements {Scope} actor input := flowWithResources … (actor | input.field)…
  liftTermElabM do
    let flow := mkConst (f ++ `flowWithResources)
    forallTelescope (← inferType flow) fun outer result => do
      let resources := outer[0]!
      let requirements := outer[1]!
      let scope := outer[2]!
      let args := outer.extract 3 outer.size
      let actorFamily ← if let some i := shape.params.findIdx? (·.actor) then mkLambdaFVars #[scope] (← inferType args[i]!)
        else pure (.lam `Scope (mkSort Level.one) (mkConst ``Unit) .default)
      Requirements.addDefinition (f ++ `Actor) (← mkArrow (mkSort Level.one) (mkSort Level.one)) actorFamily
      let inputType := mkConst inputName
      withLocalDecl `actor .default (mkApp (mkConst (f ++ `Actor)) scope) fun actor => do
      withLocalDecl `input .default inputType fun input => do
        let mut callArgs := #[]
        for p in shape.params do
          if p.actor then callArgs := callArgs.push actor
          else callArgs := callArgs.push (← mkAppM (inputName ++ p.name) #[input])
        let invocation := mkAppN flow (#[resources, requirements, scope] ++ callArgs)
        let binders := #[resources, requirements, scope, actor, input]
        Requirements.addDefinition (f ++ `bodyWithResources) (← mkForallFVars binders result) (← mkLambdaFVars binders invocation)
  let ns := f.getPrefix
  let namespaceText := if ns.isAnonymous then "domain" else ns.toString
  let q := Deriving.quoted
  let identity := "{ namespaceName := " ++ q namespaceText ++ ", name := " ++ q f.getString! ++ ", version := \"1\" }"
  let failures ← liftTermElabM <| failuresOf shape.error
  let actorText ← liftTermElabM do
    if let some p := shape.params.find? (·.actor) then return (← ppExpr p.type).pretty else return "Unit"
  let nodesText := String.intercalate ", " (nodes.toList.map fun n =>
    "{ kind := " ++ q n.kind ++ ", effect := ." ++ kindSyntax n.effect ++ ", detail := " ++ q n.detail ++
    ", failure := " ++ (n.failure.map (fun s => "some " ++ q s) |>.getD "none") ++
    ", constraints := [" ++ String.intercalate ", " (n.constraints.map q) ++ "] }")
  let pos := (ref.getPos?.map fun position => position.byteIdx).getD 0
  let location := (← getEnv).mainModule.toString.replace "." "/" ++ ".lean:" ++ toString pos
  let kdfText := String.intercalate ", " (kdf.map fun
    | .hash field => "LeanApi.Core.KdfStep.hash " ++ q field
    | .verify field => "LeanApi.Core.KdfStep.verify " ++ q field)
  let session := nodes.any (·.kind == "startSession")
  let metadata := "{ identity := " ++ identity ++ ", kind := ." ++ kindSyntax shape.kind ++ ", failures := [" ++
    String.intercalate ", " (failures.map q) ++ "], source := " ++ q location ++ ", actor := " ++ q actorText ++
    ", nodes := [" ++ nodesText ++ "], establishesSession := " ++ toString session ++ ", kdf := [" ++ kdfText ++ "] }"
  let errorText ← liftTermElabM <| Deriving.sourceOf shape.error
  let outputText ← liftTermElabM <| Deriving.sourceOf shape.output
  Deriving.runCommand ("def " ++ full (f ++ `operation) ++ " : LeanApi.Core.Operation ." ++ kindSyntax shape.kind ++ " " ++
    full (f ++ `Actor) ++ " " ++ full inputName ++ " (" ++ outputText ++ ") (" ++ errorText ++ ") := { contract := Contract.Operation.ofValidated ." ++
    kindSyntax shape.kind ++ " " ++ identity ++ " (by decide), Requirements := " ++ full (f ++ `Requirements) ++
    ", portable := " ++ full (f ++ `portableRequirements) ++ ", bodyWithResources := " ++ full (f ++ `bodyWithResources) ++
    ", metadata := " ++ metadata ++ " }")
  -- `post "/x" f` / `get "/x" f` find the operation through the function value.
  if (← getEnv).contains `LeanApi.Core.PublishedOperation then
    Deriving.runCommand ("instance : LeanApi.Core.PublishedOperation " ++ full f ++ " ." ++ kindSyntax shape.kind ++ " " ++
      full (f ++ `Actor) ++ " " ++ full inputName ++ " (" ++ outputText ++ ") (" ++ errorText ++ ") := ⟨" ++ full (f ++ `operation) ++ "⟩")

end LeanApi.Core.Publish

namespace LeanApi.Core
open Lean Elab Command

/-- Publish a plain operation: derive its input record, closed error, output, actor, typed
requirements and resource-generic body. An `Api` declaration runs this for each listed
function. -/
syntax (name := deriveOperationCmd) "derive_operation " ident : command

elab_rules : command
  | `(derive_operation $f:ident) => do
    let name ← liftCoreM <| realizeGlobalConstNoOverload f
    Publish.deriveOperation name f

end LeanApi.Core
