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

/-- Argument supplied to named parameter `paramName` of request constructor `c`. -/
private def requestNamedArg? (c paramName : Lean.Name) (args : Array Expr) : MetaM (Option Expr) := do
  forallTelescope (← getConstInfo c).type fun binders _ => do
    let names ← binders.mapM fun b => return (← b.fvarId!.getDecl).userName
    return names.findIdx? (· == paramName) >>= (args[·]?)

/-- The entity argument (`T`) of an operation-level request, if any. -/
private def requestEntity (c : Lean.Name) (args : Array Expr) : MetaM String := do
  match ← requestNamedArg? c `T args with
  | some (.const t _) => return t.toString
  | _ => return ""

/-- Ordered storage steps, operation requests, guards, and KDF input fields of an operation
body, collected in a single pass over the request structure. -/
partial def scanFlow (f : Lean.Name) (params : Array Lean.Name) (actors : Array Bool) (inlined : Expr) :
    MetaM (Array Node × List KdfStep) := do
  lambdaTelescope inlined fun binders body => do
    let nodes ← IO.mkRef (#[] : Array Node)
    let kdf ← IO.mkRef (#[] : Array KdfStep)
    let kdfError ← IO.mkRef (none : Option String)
    let checkKdf (kind : String) (password : Expr) : MetaM Unit := do
      if (← kdfError.get).isSome then return
      let password := password.consumeMData
      match binders.findIdx? (· == password) with
      | some i =>
        if i < params.size then
          if actors[i]! then
            kdfError.set (some s!"its {kind} input is the actor")
          else
            let field := params[i]!.toString
            let step := if kind == "Password.hash" then KdfStep.hash field else KdfStep.verify field
            unless (← kdf.get).contains step do kdf.modify (·.push step)
        else
          kdfError.set (some s!"its {kind} input is not an argument of `{f}`")
      | none =>
        kdfError.set (some s!"`{kind}` must be applied directly to a `Password` argument of `{f}`")
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
          nodes.modify (·.push { kind := node.kind, effect, detail := node.entity, constraints := node.constraints })
        else if let .const c _ := fn then
          if let some (_, effect) := operationRequests.find? (·.1 == c) then
            let detail ← requestEntity c args
            nodes.modify (·.push { kind := c.getString!, effect, detail })
            if c == ``RequestF.hashPassword then
              if let some pw ← requestNamedArg? c `password args then
                checkKdf "Password.hash" pw
            else if c == ``RequestF.verifyCredential then
              if let some pw ← requestNamedArg? c `password args then
                checkKdf "Credential.verify" pw
          else if (c == ``FlowF.check || c == ``Flow.check || c == ``MonadRequire.requireWith) && args.size >= 6 &&
              !args.back!.hasLooseBVars then
            nodes.modify (·.push { kind := "require", effect := .query, detail := "", failure := ← failureOf args.back! })
          else if (c == ``FlowF.fail || c == ``Flow.fail || c == ``MonadExcept.throw || c == ``MonadExceptOf.throw) &&
              args.size ≥ 4 && !args.back!.hasLooseBVars then
            nodes.modify (·.push { kind := "throw", effect := .query, detail := "", failure := ← failureOf args.back! })
        visit fn
        for arg in args do visit arg
      | .lam _ _ b _ => visit b
      | .forallE .. => pure ()
      | .letE _ _ v b _ =>
        let v' := v.consumeMData
        if binders.contains v' then visit (b.instantiate1 v')
        else visit v; visit b
      | .mdata _ b => visit b
      | .proj _ _ b => visit b
      | _ => pure ()
    visit body
    if let some problem ← kdfError.get then
      throwError "cannot publish `{f}`: {problem}, so the runtime cannot run the KDF before writer admission"
    return (← nodes.get, (← kdf.get).toList)

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

private def kindTerm : Contract.OperationKind → Term
  | .command => mkIdent ``Contract.OperationKind.command
  | .query => mkIdent ``Contract.OperationKind.query

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
  let rootIdent := LeanApi.Core.Declarations.rootIdent
  let delabTerm := LeanApi.Core.Declarations.delabTerm
  let inputs := shape.params.filter (!·.actor)
  let inputName := f ++ `Input
  let inputIdent := rootIdent inputName
  if inputs.isEmpty then
    elabCommand (← `(abbrev $inputIdent := Unit))
  else
    let fieldDecls ← liftTermElabM <| inputs.mapM (m := TermElabM) fun p => do
      let fieldId := mkIdent p.name
      let fieldTy ← delabTerm p.type
      `(Lean.Parser.Command.structSimpleBinder| $fieldId:ident : $fieldTy)
    let fieldsStx : TSyntax ``Lean.Parser.Command.structFields :=
      ⟨Syntax.node .none ``Lean.Parser.Command.structFields #[mkNullNode (fieldDecls.map (·.raw))]⟩
    let ctorId := mkIdent `mk
    elabCommand (← `(structure $inputIdent where $ctorId:ident :: $fieldsStx:structFields deriving LeanDb.Model.Domain))
    if inputs.size == 1 && (← liftTermElabM (whnfR inputs[0]!.type)).isAppOfArity ``Ontology.EntityId 1 then
      let target ← liftTermElabM do delabTerm (← whnfR inputs[0]!.type).appArg!
      let mkIdent' := rootIdent (inputName ++ `mk)
      let projIdent := rootIdent (inputName ++ inputs[0]!.name)
      elabCommand (← `(instance : LeanApi.Core.RouteInput $inputIdent :=
        { Target := $target, targetIdentity := inferInstance,
          parse := fun raw => (Ontology.Ref.parse (T := $target) raw).map $mkIdent',
          reference := $projIdent }))
  let (nodes, kdf) ← liftTermElabM do
    let generalized ← Requirements.generalize targets f (f ++ `flowWithResources)
    scanFlow f (shape.params.map (·.name)) (shape.params.map (·.actor)) generalized.inlined
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
  let identity ← `({ namespaceName := $(quote namespaceText), name := $(quote f.getString!), version := "1" })
  let failures ← liftTermElabM <| failuresOf shape.error
  let failureTerms : Array Term := failures.toArray.map fun s => quote s
  let actorText ← liftTermElabM do
    if let some p := shape.params.find? (·.actor) then return (← ppExpr p.type).pretty else return "Unit"
  let nodeTerms : Array Term ← nodes.mapM fun n => do
    let failTerm ← match n.failure with
      | some s => `(some $(quote s))
      | none => `(none)
    let constraintTerms : Array Term := n.constraints.toArray.map fun s => quote s
    let eff := kindTerm n.effect
    `({ kind := $(quote n.kind), effect := $eff, detail := $(quote n.detail), failure := $failTerm, constraints := [$constraintTerms,*] })
  let pos := (ref.getPos?.map fun position => position.byteIdx).getD 0
  let location := (← getEnv).mainModule.toString.replace "." "/" ++ ".lean:" ++ toString pos
  let kdfTerms : Array Term ← kdf.toArray.mapM fun
    | .hash field => `(LeanApi.Core.KdfStep.hash $(quote field))
    | .verify field => `(LeanApi.Core.KdfStep.verify $(quote field))
  let session := nodes.any (·.kind == "startSession")
  let kind := kindTerm shape.kind
  let opIdent := rootIdent (f ++ `operation)
  let reqIdent := rootIdent (f ++ `Requirements)
  let portIdent := rootIdent (f ++ `portableRequirements)
  let bodyIdent := rootIdent (f ++ `bodyWithResources)
  let actorIdent := rootIdent (f ++ `Actor)
  let errorTerm ← liftTermElabM <| delabTerm shape.error
  let outputTerm ← liftTermElabM <| delabTerm shape.output
  elabCommand (← `(def $opIdent : LeanApi.Core.Operation $kind $actorIdent $inputIdent ($outputTerm) ($errorTerm) :=
    { contract := Contract.Operation.ofValidated $kind $identity (by decide),
      Requirements := $reqIdent,
      portable := $portIdent,
      bodyWithResources := $bodyIdent,
      metadata := {
        identity := $identity, kind := $kind, failures := [$failureTerms,*],
        source := $(quote location), actor := $(quote actorText),
        nodes := [$nodeTerms,*], establishesSession := $(quote session), kdf := [$kdfTerms,*] } }))
  -- `post "/x" f` / `get "/x" f` find the operation through the function value.
  if (← getEnv).contains `LeanApi.Core.PublishedOperation then
    let fIdent := rootIdent f
    let pubClassIdent := rootIdent `LeanApi.Core.PublishedOperation
    elabCommand (← `(instance : $pubClassIdent $fIdent $kind $actorIdent $inputIdent ($outputTerm) ($errorTerm) :=
      ⟨$opIdent⟩))

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
