/-
  Authoring (PLAN.md M9): define an invariant once, get the runtime check,
  the per-command obligations, and routine proofs.

  ```
  invariant Valid (g : Game) where
    distinct : g.x ≠ g.o
    nodup    : (g.moves.map (·.i)).Nodup
    proof_only deep : SomeUndecidableFact g

  preserves Valid by openGame, playMove, resign
    | playMove => ...   -- only the goals `invariant_cases` could not close
  ```

  `invariant N (x : α) where fields` generates plain declarations a user
  could have written by hand:

  * `structure N (x : α) : Prop` with the fields;
  * `N.fields x : List (String × Bool)`: each checkable field, decided;
  * `N.holdsB x : Bool` and `N.check x : Except (List String) Unit`, which
    names the failing fields;
  * `N.holdsB_iff : N.holdsB x = true ↔ N x` and `N.check_iff`, plus a
    `Decidable (N x)` instance. With `proof_only` fields, only the sound
    direction (`N.holdsB_of`, `N.check_of`) is generated and there is no
    instance: the runtime check is then weaker than the property;
  * a registry entry.

  A field that is not decidable and not marked `proof_only` is an error that
  names the field.

  `preserves N by f₁, f₂` generates, for each decision function
  `f : … → α → Except ε α` (the state is the last argument of type `α`; a
  function with no such argument is a constructor), the theorem
  `N.preserved_f : ∀ args s', N s → f args = .ok s' → N s'` (or
  `f args = .ok s' → N s'`). It runs `invariant_cases`, then the optional
  tactic given for that function. If goals remain, the command fails and
  lists each one by field.
-/
import Lean
import LeanApi.Props.Registry

namespace LeanApi.Props

open Lean Elab Command Term Meta Tactic

/-! ## Runtime checks from field lists -/

/-- Names of the failing checks, or `ok`. -/
def Checks.run (l : List (String × Bool)) : Except (List String) Unit :=
  match l.filterMap (fun (n, b) => if b then none else some n) with
  | [] => .ok ()
  | es => .error es

theorem Checks.failing_nil_iff (l : List (String × Bool)) :
    l.filterMap (fun (n, b) => if b then none else some n) = [] ↔ l.all (·.2) = true := by
  induction l with
  | nil => simp
  | cons a l ih => obtain ⟨n, b⟩ := a; cases b <;> simp [ih]

theorem Checks.run_ok_iff (l : List (String × Bool)) : Checks.run l = .ok () ↔ l.all (·.2) = true := by
  unfold Checks.run
  rw [← Checks.failing_nil_iff]
  split <;> simp_all

/-! ## Registry of invariants -/

structure InvEntry where
  name : Name
  carrier : String
  fields : Array Name
  proofOnly : Array Name
  deriving Inhabited

structure PreservesEntry where
  inv : Name
  fn : Name
  thm : Name
  deriving Inhabited

initialize invariantExt : SimplePersistentEnvExtension InvEntry (Array InvEntry) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun as => as.foldl (· ++ ·) #[] }

initialize preservesExt : SimplePersistentEnvExtension PreservesEntry (Array PreservesEntry) ←
  registerSimplePersistentEnvExtension { addEntryFn := Array.push, addImportedFn := fun as => as.foldl (· ++ ·) #[] }

def allInvariants (env : Environment) : Array InvEntry := invariantExt.getState env
def allPreserves (env : Environment) : Array PreservesEntry := preservesExt.getState env

def findInvariant? (env : Environment) (n : Name) : Option InvEntry :=
  (allInvariants env).find? (·.name == n)

/-! ## `invariant` -/

syntax invField := ppLine withPosition((&"proof_only ")? ident " : " term)

/-- Declare an invariant; see the module docstring. -/
syntax (name := invariantCmd) (docComment)? "invariant " ident "(" ident " : " term ")" " where" invField+ : command

/-- `h.2.2…1`: the `i`-th component of an `n`-fold right-nested conjunction. -/
def conjProj (h : Term) (i n : Nat) : MacroM Term := do
  let mut t := h
  for _ in [0:i] do t ← `(And.right $t)
  if i + 1 < n then `(And.left $t) else pure t

/-- `⟨a₁, ⟨a₂, … aₙ⟩⟩` as a right-nested `And.intro`. -/
def conjIntro : List Term → MacroM Term
  | [] => `(True.intro)
  | [a] => pure a
  | a :: as => do `(And.intro $a $(← conjIntro as))

elab_rules : command
  | `($[$doc?]? invariant $n:ident ($x:ident : $t:term) where $fs:invField*) => do
    let parsed := fs.map fun f => match f with
      | `(invField| $[proof_only%$po]? $fid:ident : $ty:term) => (po.isSome, fid, ty)
      | _ => (false, ⟨.missing⟩, ⟨.missing⟩)
    -- the Prop structure
    let fids := parsed.map (·.2.1)
    let ftys := parsed.map (·.2.2)
    elabCommand (← `($[$doc?]? structure $n ($x : $t) : Prop where $[$fids:ident : $ftys]*))
    let checked := parsed.filter (!·.1)
    let proofOnly := parsed.filter (·.1)
    -- every checked field must be decidable
    for (_, fid, ty) in checked do
      let ok ← liftTermElabM do
        try
          let _ ← Term.withoutErrToSorry do
            let e ← Term.elabTerm (← `(fun ($x : $t) => (decide ($ty) : Bool))) none
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e
          pure true
        catch _ => pure false
      unless ok do
        throwErrorAt fid "invariant: field `{fid.getId}` is not decidable, so no runtime check can be derived \
from it. Add a `Decidable` instance for its statement, or mark it `proof_only` (it is then proved but \
left out of `{n.getId}.check`)."
    let nm (s : String) : Ident := mkIdent (n.getId ++ Name.mkSimple s)
    let pairs ← checked.mapM fun (_, fid, ty) => `(($(quote fid.getId.toString), decide ($ty)))
    elabCommand (← `(/-- The checkable fields of the invariant, decided. -/
      def $(nm "fields") ($x : $t) : List (String × Bool) := [$pairs,*]))
    elabCommand (← `(/-- The runtime check. -/
      def $(nm "holdsB") ($x : $t) : Bool := ($(nm "fields") $x).all (·.2)))
    elabCommand (← `(/-- The runtime check, naming every failing field. -/
      def $(nm "check") ($x : $t) : Except (List String) Unit := LeanApi.Props.Checks.run ($(nm "fields") $x)))
    let simpSet ← `(tactic| simp only [$(nm "holdsB"):ident, $(nm "fields"):ident, List.all_cons, List.all_nil,
        Bool.and_true, Bool.and_eq_true, decide_eq_true_eq])
    let k := checked.size
    let h := mkIdent `h
    let v := mkIdent `v
    if proofOnly.isEmpty then
      -- holdsB = true ↔ N x
      let toStruct ← liftMacroM <| (List.range k).mapM fun i => conjProj h i k
      let toConj ← liftMacroM <| conjIntro (checked.toList.map fun (_, fid, _) =>
        (mkIdent (v.getId ++ fid.getId) : Term))
      let parts := toStruct.toArray
      let mk ← `(⟨$parts,*⟩)
      elabCommand (← `(theorem $(nm "holdsB_iff") ($x : $t) : $(nm "holdsB") $x = true ↔ $n $x := by
        $simpSet:tactic
        exact ⟨fun $h => $mk, fun $v => $toConj⟩))
      elabCommand (← `(theorem $(nm "check_iff") ($x : $t) : $(nm "check") $x = .ok () ↔ $n $x :=
        (LeanApi.Props.Checks.run_ok_iff _).trans ($(nm "holdsB_iff") $x)))
      elabCommand (← `(instance ($x : $t) : Decidable ($n $x) := decidable_of_iff _ ($(nm "holdsB_iff") $x)))
    else
      let toConj ← liftMacroM <| conjIntro (checked.toList.map fun (_, fid, _) =>
        (mkIdent (v.getId ++ fid.getId) : Term))
      elabCommand (← `(/-- Sound direction only: some fields are `proof_only`. -/
        theorem $(nm "holdsB_of") ($x : $t) ($v : $n $x) : $(nm "holdsB") $x = true := by
        $simpSet:tactic
        exact $toConj))
      elabCommand (← `(theorem $(nm "check_of") ($x : $t) ($v : $n $x) : $(nm "check") $x = .ok () :=
        (LeanApi.Props.Checks.run_ok_iff _).mpr ($(nm "holdsB_of") $x $v)))
    let full := (← getCurrNamespace) ++ n.getId
    let full := if (← getEnv).contains full then full else n.getId
    modifyEnv (invariantExt.addEntry · {
      name := full, carrier := toString t.raw.prettyPrint,
      fields := checked.map (·.2.1.getId), proofOnly := proofOnly.map (·.2.1.getId) })

/-! ## `invariant_cases` -/

/-- Run `tac` on `g` without error recovery; on failure, undo everything. -/
def tryOn (g : MVarId) (tac : TacticM Unit) : TacticM (Option (List MVarId)) := do
  let s ← saveState
  let errCount : TacticM Nat := do
    return (← Core.getMessageLog).toList.filter (·.severity == .error) |>.length
  let before ← errCount
  try
    let gs ← Tactic.run g (withoutRecover tac)
    -- `done` and friends log an error and abort instead of throwing
    if (← errCount) > before then
      s.restore
      return none
    return some gs
  catch _ =>
    s.restore
    return none


/-- Give readable names to the inaccessible hypotheses `split` introduced:
    the branch conditions become `c₁, c₂, …`. -/
def nameBranchConditions (g : MVarId) : MetaM MVarId := g.withContext do
  let mut g := g
  let mut k := 1
  for d in (← getLCtx) do
    if d.isImplementationDetail then continue
    if d.userName.hasMacroScopes && (← isProp d.type) then
      g ← g.rename d.fvarId (Name.mkSimple s!"c{k}")
      k := k + 1
  return g

/-- Split `h : f … = .ok s'` into its branches: refusals are closed, and in
    each accepting branch `s'` is replaced by the value built. -/
partial def splitDecision (h : Name) (g : MVarId) : TacticM (List MVarId) := do
  -- a refusal (`.error _ = .ok _`) closes; an acceptance substitutes
  let tryCases : TacticM (Option (List MVarId)) := do
    tryOn g (evalTactic (← `(tactic| cases $(mkIdent h):ident)))
  let ty ← g.withContext do
    let some d := (← getLCtx).findFromUserName? h | throwError "invariant_cases: no hypothesis `{h}`"
    whnfR (← instantiateMVars d.type)
  let isCtorEq : MetaM Bool := do
    match ty.eq? with
    | some (_, lhs, _) => return (← whnfR lhs).getAppFn.isConstOf ``Except.ok || (← whnfR lhs).getAppFn.isConstOf ``Except.error
    | none => return false
  if ← isCtorEq then
    if let some gs ← tryCases then return gs
  match ← tryOn g (evalTactic (← `(tactic| split at $(mkIdent h):ident))) with
  | some gs => return (← gs.mapM (splitDecision h)).flatten
  | none =>
    if let some gs ← tryCases then return gs
    return [g]

/-- The per-field closers, in order: the field is untouched (frame: it is
    `hI.field` after reducing projections), or follows by `simp_all` with
    the given lemmas and the fields of `hI` in context (then `omega`), or by
    `omega`, or by `decide`. -/
def closeField (hI : Option Name) (lemmas : Array Term) (g : MVarId) : TacticM (List MVarId) := do
  let tag ← g.getTag
  let field := tag.eraseMacroScopes.components.getLast?.getD tag
  let args : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← lemmas.mapM fun l =>
    `(Lean.Parser.Tactic.simpLemma| $l:term)
  -- reduce `{ g with … }.field` in the goal
  let g := match ← tryOn g (evalTactic (← `(tactic| dsimp only))) with
    | some [g'] => g'
    | _ => g
  -- the fields of the hypothesis, as named local facts
  let withFields : TacticM Unit := do
    if let some hI := hI then
      let env ← getEnv
      let ty ← g.withContext do
        let some d := (← getLCtx).findFromUserName? hI | throwError "no {hI}"
        whnfR (← instantiateMVars d.type)
      if let some sn := ty.getAppFn.constName? then
        if isStructure env sn then
          for f in getStructureFields env sn do
            let nm := mkIdent (Name.mkSimple s!"{hI}_{f}")
            evalTactic (← `(tactic| have $nm := $(mkIdent (hI ++ f)):ident))
  let attempts : List (TacticM Unit) :=
    (match hI with
     | some hI => [do evalTactic (← `(tactic| exact $(mkIdent (hI ++ field)):ident))]
     | none => []) ++
    [ do evalTactic (← `(tactic| (simp_all [$args,*]; done))),
      do withFields; evalTactic (← `(tactic| (simp_all [$args,*]; done))),
      do withFields; evalTactic (← `(tactic| (simp_all [$args,*]; omega))),
      do withFields; evalTactic (← `(tactic| omega)),
      do evalTactic (← `(tactic| decide)) ]
  for a in attempts do
    if let some [] ← tryOn g a then return []
  return [g]

/-- Unfold the decision in `h`, split on its branches, close refusals, split
    the invariant into fields, and close every routine field. The remaining
    goals are tagged with the field name; branch conditions are `c₁, c₂, …`. -/
def invariantCasesCore (h : Name) (hI : Option Name) (lemmas : Array Term) : TacticM Unit := do
  let g ← getMainGoal
  -- unfold the head constant of the decision
  let fn? ← g.withContext do
    let some d := (← getLCtx).findFromUserName? h | throwError "invariant_cases: no hypothesis `{h}`"
    match (← instantiateMVars d.type).eq? with
    | some (_, lhs, _) => pure lhs.getAppFn.constName?
    | none => pure none
  let g ← match fn? with
    | some f =>
      match ← tryOn g (evalTactic (← `(tactic| unfold $(mkIdent f):ident at $(mkIdent h):ident))) with
      | some [g'] => pure g'
      | _ => pure g
    | none => pure g
  let branches ← splitDecision h g
  let mut remaining := []
  for b in branches do
    let b ← nameBranchConditions b
    let fields := (← tryOn b (evalTactic (← `(tactic| constructor)))).getD [b]
    for fg in fields do
      remaining := remaining ++ (← closeField hI lemmas fg)
  replaceMainGoal remaining

/-- `invariant_cases [lemmas] at h using hI` (defaults: `h`, `hI`). -/
syntax (name := invariantCases) "invariant_cases" (" [" term,* "]")? (" at " ident)? (" using " ident)? : tactic

elab_rules : tactic
  | `(tactic| invariant_cases $[[$ls,*]]? $[at $h]? $[using $hI]?) => do
    let h := (h.map (·.getId)).getD `h
    let hI := (hI.map (·.getId)).getD `hI
    let hasHI ← (← getMainGoal).withContext do return ((← getLCtx).findFromUserName? hI).isSome
    invariantCasesCore h (if hasHI then some hI else none) ((ls.map (·.getElems)).getD #[])

/-! ## `preserves` -/

/-- The obligation for `f` (see the module docstring), with the names of
    the binders to introduce. -/
def preservesType (inv f : Name) : MetaM (Expr × Array Name × Bool) := do
  let invTy ← inferType (mkConst inv)
  let α ← forallTelescopeReducing invTy fun xs _ => do
    unless xs.size == 1 do throwError "preserves: `{inv}` must take exactly one argument"
    inferType xs[0]!
  let fTy ← inferType (← mkConstWithFreshMVarLevels f)
  forallTelescopeReducing fTy fun xs res => do
    let res ← whnfR res
    unless res.isAppOfArity ``Except 2 do
      throwError "preserves: `{f}` must return `Except ε {α}`, but returns{indentExpr res}"
    unless ← isDefEq res.appArg! α do
      throwError "preserves: `{f}` returns `Except _ {res.appArg!}`, not the invariant's carrier `{α}`"
    let mut stateIdx : Option Nat := none
    for i in [0:xs.size] do
      if ← isDefEq (← inferType xs[i]!) α then stateIdx := some i
    let names ← xs.mapIdxM fun i x => do
      let n := (← x.fvarId!.getDecl).userName
      pure (if n.hasMacroScopes || n.isAnonymous then Name.mkSimple s!"a{i}" else n)
    withLocalDeclD `s' α fun s' => do
      let ok ← mkAppOptM ``Except.ok #[res.appFn!.appArg!, α, s']
      let heq ← mkEq (mkAppN (← mkConstWithFreshMVarLevels f) xs) ok
      let concl := mkApp (mkConst inv) s'
      let body ← match stateIdx with
        | some i => do
          let pre := mkApp (mkConst inv) xs[i]!
          withLocalDeclD `hI pre fun hI => withLocalDeclD `h heq fun h => do
            mkForallFVars (xs.push s' |>.push hI |>.push h) concl
        | none => withLocalDeclD `h heq fun h => mkForallFVars (xs.push s' |>.push h) concl
      let body ← instantiateMVars body
      let names := names.push `s' ++ (if stateIdx.isSome then #[`hI, `h] else #[`h])
      return (body, names, stateIdx.isSome)

syntax preservesAlt := ppLine "| " ident " => " tacticSeq

/-- `preserves N by f₁, f₂ [using [lemmas]] (| fᵢ => tactic)*`. -/
syntax (name := preservesCmd) "preserves " ident " by " ident,+ (" using " "[" term,* "]")? preservesAlt* : command

elab_rules : command
  | `(preserves $inv:ident by $fs,* $[using [$ls,*]]? $alts:preservesAlt*) => do
    let invName ← liftCoreM (realizeGlobalConstNoOverloadWithInfo inv)
    if (findInvariant? (← getEnv) invName).isNone then
      logWarning m!"preserves: `{invName}` was not declared with `invariant`; generating obligations anyway"
    let lemmas := (ls.map (·.getElems)).getD #[]
    let altMap ← alts.mapM fun a => match a with
      | `(preservesAlt| | $f:ident => $tac:tacticSeq) => do
        pure ((← liftCoreM (realizeGlobalConstNoOverloadWithInfo f)), tac)
      | _ => throwUnsupportedSyntax
    let mut failures : Array MessageData := #[]
    for fid in fs.getElems do
      let f ← liftCoreM (realizeGlobalConstNoOverloadWithInfo fid)
      let thmName := invName ++ Name.mkSimple s!"preserved_{f.getString!}"
      let (ty, names, _) ← liftTermElabM (preservesType invName f)
      let userTac := altMap.find? (·.1 == f) |>.map (·.2)
      let result ← liftTermElabM do
        let mvar ← mkFreshExprMVar ty (kind := .syntheticOpaque)
        let ids := names.map mkIdent
        let remaining ← Term.withoutErrToSorry <| Tactic.run mvar.mvarId! <| withoutRecover do
          evalTactic (← `(tactic| intro $ids*))
          evalTactic (← `(tactic| invariant_cases [$lemmas,*]))
          if let some tac := userTac then
            unless (← getGoals).isEmpty do
              evalTactic tac
        if remaining.isEmpty then
          let val ← instantiateMVars mvar
          if val.hasMVar then throwError "preserves: proof of `{thmName}` has unassigned metavariables"
          if val.hasSorry then throwError "preserves: proof of `{thmName}` uses `sorry`"
          pure (Sum.inr val)
        else
          pure (Sum.inl (MessageData.joinSep (← remaining.mapM fun g => do
            pure (indentD (← Meta.ppGoal g))) "\n"))
      match result with
      | .inr val =>
        liftTermElabM do
          addDecl (.thmDecl { name := thmName, levelParams := [], type := ty, value := val })
          addDocStringCore thmName s!"`{f}` preserves `{invName}` (generated by `preserves`)."
        modifyEnv (preservesExt.addEntry · { inv := invName, fn := f, thm := thmName })
      | .inl goals =>
        failures := failures.push m!"`{f}` ({thmName}) leaves:\n{goals}"
    unless failures.isEmpty do
      throwError "preserves: `invariant_cases` could not close every obligation. Add a case \
`| f => tactic` for each function below; the goals are tagged by field and the branch conditions \
are named `c₁, c₂, …`.\n\n{MessageData.joinSep failures.toList "\n\n"}"

end LeanApi.Props
