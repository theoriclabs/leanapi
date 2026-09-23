/-
  Check before proving (PLAN.md M10, PROPERTIES.md §5.2, §6.4, §6.5).

  `#check_invariant I on S using spec` reports, over the finite search space
  `spec` (small worlds, environments, requests):

  * **well-formedness**: `I` is decidable (else an error naming the fix);
    the carrier; and a warning when the world stores a `List` but the spec
    gives no `reorder` to test that `I` respects permutation (§6.4);
  * **initial worlds**: every searched initial world must satisfy `I`
    (`Inductive.init`). One that does not makes `I` false, and the report
    never says "inductive" then;
  * **vacuity**: an initial world satisfying `I`, and a world violating it.
    If `I` rules nothing out, or admits no initial world, it says so;
  * **counterexamples to induction**: a world satisfying `I`, a request,
    and the fields the successor violates. For each CTI it says whether the
    world is reachable from the searched initial worlds (with the path
    length), which decides between "`I` is false" and "`I` needs
    strengthening";
  * **next candidate**: whether `I ∧ pre I` (over the searched requests)
    still has CTIs.

  `checkHidden` is the hiddenness-witness check for observations (§5.2):
  for each observer, two different worlds with the same view. An
  observation whose view determines the world (review C1) fails it.

  The search is bounded and reports what it searched. Proofs never depend
  on it.
-/
import LeanApi.Props.Sys
import LeanApi.Props.Enumerate

namespace LeanApi.Props

/-- The finite search space. -/
structure CheckSpec (S : Sys) where
  worlds : List S.World
  envs : List S.Env
  reqs : List S.Req
  initB : S.World → Bool
  beq : S.World → S.World → Bool
  showW : S.World → String
  showR : S.Req → String
  /-- Depth of the reachability search from the initial worlds. -/
  depth : Nat := 3
  /-- Other representations of the same world (for example, the same
      entities in another order). `I` must agree on all of them. -/
  reorder : Option (S.World → List S.World) := none

structure CTIReport where
  world : String
  req : String
  failing : List String
  /-- Path length from an initial world, when found. -/
  reachableAt : Option Nat
  deriving Repr

structure InvReport where
  name : String
  searched : Nat × Nat × Nat
  initWitness : Option String
  /-- Searched initial worlds that violate `I`: the invariant is false. -/
  initViolations : List String
  /-- Depth of the reachability search, for reporting its bound. -/
  depth : Nat
  violating : Option String
  ctis : List CTIReport
  /-- CTIs of `I ∧ pre I` (over the searched requests). -/
  strengthenedCtis : Nat
  reorderBreaks : Option (String × String)
  warnings : List String
  deriving Repr

namespace InvReport

def vacuous (r : InvReport) : Bool := r.initWitness.isNone || r.violating.isNone

def render (r : InvReport) : String := Id.run do
  let (nw, ne, nr) := r.searched
  let mut out := [s!"#check_invariant {r.name}: searched {nw} worlds × {ne} environments × {nr} requests"]
  for w in r.warnings do out := out ++ [s!"  warning: {w}"]
  match r.initWitness with
  | some w => out := out ++ [s!"  ✓ satisfiable: initial world {w}"]
  | none => out := out ++ ["  ✗ vacuous: no searched initial world satisfies the invariant"]
  unless r.initViolations.isEmpty do
    out := out ++ [s!"  ✗ false initially: {r.initViolations.length} searched initial world(s) violate the \
invariant, e.g. {r.initViolations.head!}. An invariant must hold in every initial world"]
  match r.violating with
  | some w => out := out ++ [s!"  ✓ restrictive: rules out {w}"]
  | none => out := out ++ ["  ✗ vacuous: no searched world violates the invariant (it may be `True`)"]
  if let some (a, b) := r.reorderBreaks then
    out := out ++ [s!"  ✗ representation-dependent: holds for {a} but not for its reordering {b}"]
  if r.ctis.isEmpty && !r.initViolations.isEmpty then
    out := out ++ ["  ✗ not inductive: no counterexample to induction among the searched steps, but it fails \
in an initial world (above)"]
  else if r.ctis.isEmpty then
    out := out ++ ["  ✓ inductive within the bound: no counterexample to induction"]
  else
    out := out ++ [s!"  ✗ not inductive: {r.ctis.length} counterexample(s) to induction"]
    for c in r.ctis.take 3 do
      let reach := match c.reachableAt with
        | some k => s!"REACHABLE in {k} step(s) from an initial world (per the spec's `initB`): the invariant is false"
        | none => s!"not reached within {r.depth} step(s) of the searched initial worlds: if it is unreachable, \
strengthen the invariant to exclude it; if it is reachable at a greater depth, the invariant is false"
      out := out ++ [s!"    world {c.world}", s!"      request {c.req} breaks {c.failing}", s!"      {reach}"]
    if r.strengthenedCtis == 0 then
      out := out ++ ["  candidate strengthening `I ∧ pre I`: inductive within the bound"]
    else
      out := out ++ [s!"  candidate strengthening `I ∧ pre I`: still {r.strengthenedCtis} CTI(s); \
look for the missing conjunct the CTI worlds share"]
  return "\n".intercalate out

end InvReport

/-- Worlds reachable within `depth` steps, with the step count. -/
def reachableWithin {S : Sys} (spec : CheckSpec S) : List (S.World × Nat) := Id.run do
  let mut seen : List (S.World × Nat) := (spec.worlds.filter spec.initB).map (·, 0)
  let mut frontier := seen.map (·.1)
  for k in [1:spec.depth + 1] do
    let mut next := []
    for w in frontier do
      for e in spec.envs do
        for r in spec.reqs do
          let w' := (S.step e r w).2
          unless seen.any (spec.beq w' ·.1) do
            seen := seen ++ [(w', k)]
            next := next ++ [w']
    frontier := next
  return seen

/-- The check itself. `fields w` names the conjuncts, for reporting which
    one fails; by default the invariant is one field. -/
def checkInvariant (S : Sys) (spec : CheckSpec S) (name : String) (I : S.World → Prop) [DecidablePred I]
    (fields : Option (S.World → List (String × Bool)) := none) (listWarning : Bool := false) : InvReport :=
  let holds (w : S.World) : Bool := decide (I w)
  let failing (w : S.World) : List String :=
    match fields with
    | some f => (f w).filterMap fun (n, b) => if b then none else some n
    | none => [name]
  let reach := reachableWithin spec
  let ctis := spec.worlds.filter holds |>.flatMap fun w =>
    spec.envs.flatMap fun e => spec.reqs.filterMap fun r =>
      let w' := (S.step e r w).2
      if holds w' then none else
        some { world := spec.showW w, req := spec.showR r, failing := failing w',
               reachableAt := (reach.find? (spec.beq w ·.1)).map (·.2) : CTIReport }
  let preI (w : S.World) : Bool := spec.envs.all fun e => spec.reqs.all fun r => holds (S.step e r w).2
  let strong (w : S.World) : Bool := holds w && preI w
  let sctis := spec.worlds.filter strong |>.foldl (fun n w =>
    n + (spec.envs.flatMap fun e => spec.reqs.filter fun r => !strong (S.step e r w).2).length) 0
  let reorderBreaks := spec.reorder.bind fun ro =>
    spec.worlds.findSome? fun w =>
      (ro w).find? (fun w' => holds w != holds w') |>.map fun w' =>
        if holds w then (spec.showW w, spec.showW w') else (spec.showW w', spec.showW w)
  let warnings :=
    if listWarning && spec.reorder.isNone then
      ["the world stores a `List`, but no `reorder` was given: the invariant is not checked to respect \
permutation. If order is not meaningful, give `reorder` in the spec, or state the invariant on a canonical form"]
    else []
  { name, searched := (spec.worlds.length, spec.envs.length, spec.reqs.length),
    initWitness := (spec.worlds.find? fun w => spec.initB w && holds w).map spec.showW,
    initViolations := (spec.worlds.filter fun w => spec.initB w && !holds w).map spec.showW,
    depth := spec.depth,
    violating := (spec.worlds.find? fun w => !holds w).map spec.showW,
    ctis, strengthenedCtis := sctis, reorderBreaks, warnings }

/-! ## Hiddenness witnesses -/

structure HiddenReport where
  observer : String
  witness : Option (String × String)
  deriving Repr

/-- For each observer, two different worlds with the same view. -/
def checkHidden {W A V : Type} [BEq V] (worlds : List W) (weq : W → W → Bool) (observers : List A)
    (view : A → W → V) (showA : A → String) (showW : W → String) : List HiddenReport :=
  observers.map fun a =>
    let pairs := worlds.flatMap fun w₁ => worlds.filterMap fun w₂ =>
      if !weq w₁ w₂ && view a w₁ == view a w₂ then some (showW w₁, showW w₂) else none
    { observer := showA a, witness := pairs.head? }

def renderHidden (rs : List HiddenReport) : String :=
  "\n".intercalate (rs.map fun r => match r.witness with
    | some (a, b) => s!"  ✓ observer {r.observer}: worlds {a} and {b} differ but look the same"
    | none => s!"  ✗ observer {r.observer}: no two searched worlds share a view. The view determines \
the world, so noninterference over it is (near-)vacuous (review C1)")

/-! ## Command -/

open Lean Elab Command Meta Term

/-- Does the world type mention `List` (in itself or its structure fields)? -/
def mentionsList (t : Expr) : MetaM Bool := do
  let t ← whnf t
  if (t.find? (·.isConstOf ``List)).isSome then return true
  let some n := t.getAppFn.constName? | return false
  let env ← getEnv
  unless isStructure env n do return false
  for f in getStructureFieldsFlattened env n (includeSubobjectFields := false) do
    let some proj := getProjFnForField? env n f | continue
    let pt ← inferType (mkConst proj (← mkConstWithFreshMVarLevels n).constLevels!)
    if (pt.find? (·.isConstOf ``List)).isSome then return true
  return false

/-- `#check_invariant I on S using spec [fields f]`: see the module docstring. -/
syntax (name := checkInvariantCmd) "#check_invariant " term:max " on " term:max " using " term:max
  (&" fields " term:max)? : command

elab_rules : command
  | `(#check_invariant $i on $s using $spec $[fields $f]?) => do
    let (listy, ok, iMsg) ← liftTermElabM do
      let sE ← elabTerm s (some (mkConst ``Sys))
      let wT := mkApp (mkConst ``Sys.World) sE
      let iE ← elabTerm i (some (← mkArrow wT (mkSort .zero)))
      synthesizeSyntheticMVarsNoPostponing
      let iE ← instantiateMVars iE
      let dec ← try
          let _ ← synthInstance (← mkAppOptM ``DecidablePred #[wT, iE]); pure true
        catch _ => pure false
      return (← mentionsList (← whnf wT), dec, (← ppExpr iE))
    unless ok do
      throwErrorAt i m!"#check_invariant: the invariant is not decidable, so it cannot be searched. Declare it \
with `invariant` (which derives the instance) or provide `DecidablePred`.{indentD iMsg}"
    let name := quote ((toString (← liftCoreM (PrettyPrinter.ppTerm i))).replace "\n" " " |>.splitOn " " |>.filter (· ≠ "") |> " ".intercalate)
    let lw := if listy then mkIdent ``true else mkIdent ``false
    let fieldsArg ← match f with
      | some f => `(some $f)
      | none => `(none)
    elabCommand (← `(#eval IO.println (LeanApi.Props.InvReport.render
      (LeanApi.Props.checkInvariant $s $spec $name $i $fieldsArg $lw))))

end LeanApi.Props
