/-
  The property registry (PLAN.md M11): properties as data that tools can
  list, so the evidence record cannot claim more than the checked theorems
  say.

  * `register_property` records a claim. A **proved** claim names a theorem.
    The status is not what the author says: it is computed when the claim is
    registered, from the theorem's axioms. A theorem that uses `sorry` or
    `native_decide`, or an axiom outside `propext`, `Classical.choice` and
    `Quot.sound`, is refused.
  * `#properties` prints the registry. `#evidence_tables` prints the claim
    tables of EVIDENCE.md, which `scripts/gen_evidence.sh` splices in.
  * Tables are declared with `declare_tables`. Writers (routes, jobs, admin
    commands) are declared with `declare_writer`, with the tables they touch,
    or as `readonly`. Unknown tables are refused.
  * `register_invariant` records a system invariant. Its first theorem must
    have the form `Invariant S I`, and the writers its proof covers are not
    written by the author: they come from the `HasWriters S` instance of the
    system `S` that theorem quantifies over (review H5, eb67460).
    `#check_writer_coverage` fails the build when a writer touches a table
    the invariant is about but is neither covered nor listed as `unproved`.
-/
import Lean
import LeanApi.Props.Sys

namespace LeanApi.Props

open Lean Elab Command Meta

inductive Status where
  | proved | checked | assumed | open
  deriving Inhabited, BEq, Repr

def Status.label : Status → String
  | .proved => "Proved" | .checked => "Checked" | .assumed => "Assumed" | .open => "Open"

structure PropEntry where
  /-- Evidence section, e.g. "Domain". -/
  section_ : String
  claim : String
  status : Status
  /-- The theorems that prove the claim (for `proved`). -/
  thms : Array Name := #[]
  /-- Where the evidence is, for non-proved claims (a test name, a file). -/
  where_ : String := ""
  /-- The shape (PROPERTIES.md §3): invariant, step, relational, ... -/
  shape : String := ""
  /-- For system invariants: tables the invariant is about. -/
  touches : Array String := #[]
  /-- For system invariants: writers its proof covers. -/
  covers : Array String := #[]
  /-- For system invariants: writers declared outside the proof. -/
  unproved : Array String := #[]
  /-- Declaration order, for stable output. -/
  order : Nat := 0
  deriving Inhabited

structure WriterEntry where
  name : String
  touches : Array String
  deriving Inhabited

/-- The writers whose steps make up system `S`: what an `Invariant S I`
    proof covers. An app gives this once per system, computed from the same
    route table (or writer list) that defines `S.step`. -/
class HasWriters (S : Sys) where
  writers : List String

initialize propertyExt : SimplePersistentEnvExtension PropEntry (Array PropEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

initialize writerExt : SimplePersistentEnvExtension WriterEntry (Array WriterEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

def allProperties (env : Environment) : Array PropEntry :=
  let es := propertyExt.getState env
  es.qsort (fun a b => a.order < b.order)

def allWriters (env : Environment) : Array WriterEntry := writerExt.getState env

initialize tableExt : SimplePersistentEnvExtension String (Array String) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun as => as.foldl (· ++ ·) #[]
  }

def allTables (env : Environment) : Array String := tableExt.getState env

def checkTables (what : String) (ts : Array String) : CommandElabM Unit := do
  let known := allTables (← getEnv)
  for t in ts do
    unless known.contains t do
      throwError "{what}: unknown table `{t}`; declare it with `declare_tables` (known: {", ".intercalate known.toList})"

/-- Axioms a proved claim may use. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- Refuse a theorem as evidence unless it exists and uses only the allowed
    axioms. This is the same rule as `scripts/axiom_audit.sh`. -/
def checkEvidenceTheorem (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains n do throwError "register_property: unknown theorem `{n}`"
  let axs ← liftCoreM (collectAxioms n)
  let bad := axs.filter (!allowedAxioms.contains ·)
  unless bad.isEmpty do
    throwError "register_property: `{n}` cannot be evidence for a proved claim: it depends on {bad.toList}"

def nextOrder : CommandElabM Nat := do
  let env ← getEnv
  return (propertyExt.getState env).size + (propertyExt.getState env |>.foldl (fun m e => max m e.order) 0) + 1

def addProperty (e : PropEntry) : CommandElabM Unit := do
  let o ← nextOrder
  modifyEnv (propertyExt.addEntry · { e with order := o })

/-! ## Commands -/

def elabStatus (id : Ident) : CommandElabM Status :=
  match id.getId with
  | `proved => pure .proved
  | `checked => pure .checked
  | `assumed => pure .assumed
  | `unproved => pure .open
  | _ => throwErrorAt id "expected a status: proved, checked, assumed or unproved (listed as Open)"

/-- Record a claim for the evidence record.

```
register_property "Domain" "Every stored game is `Valid`"
  proved by PrivateGames.Model.allValid
register_property "Isolation" "SQLite does not expose other rows" assumed
register_property "Idempotence" "Key reuse is refused" checked at "tests: keyed idempotence"
```
-/
syntax (name := registerProperty) "register_property " str str ident
  (" by " ident,+)? (" at " str)? (&" shape " str)? : command

elab_rules : command
  | `(register_property $sec:str $claim:str $st:ident $[by $thms,*]? $[at $w]? $[shape $sh]?) => do
    let status ← elabStatus st
    let thms ← (thms.map (·.getElems) |>.getD #[]).mapM fun id => do
      let n ← liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
      pure n
    if status == .proved then
      if thms.isEmpty then throwError "register_property: a proved claim must name its theorem(s) with `by`"
      thms.forM checkEvidenceTheorem
    else if !thms.isEmpty then
      throwError "register_property: only a proved claim names theorems; use `at` for other evidence"
    addProperty { section_ := sec.getString, claim := claim.getString, status, thms := thms,
                  where_ := (w.map (·.getString)).getD "", shape := (sh.map (·.getString)).getD "" }

/-- Declare the tables writers and invariants may refer to. -/
syntax (name := declareTables) "declare_tables " str,+ : command

elab_rules : command
  | `(declare_tables $ts,*) => do
    for t in ts.getElems do
      let t := t.getString
      unless (allTables (← getEnv)).contains t do
        modifyEnv (tableExt.addEntry · t)

/-- Declare a writer (route, job, admin command) and the tables it touches,
    or `readonly`. A writer that touches nothing must say so. -/
syntax (name := declareWriter) "declare_writer " str &" touches " str,+ : command
@[inherit_doc declareWriter]
syntax (name := declareReadonly) "declare_writer " str &" readonly" : command

def addWriter (name : String) (touches : Array String) : CommandElabM Unit := do
  if (allWriters (← getEnv)).any (·.name == name) then
    throwError "declare_writer: `{name}` is already declared"
  checkTables s!"declare_writer `{name}`" touches
  modifyEnv (writerExt.addEntry · { name, touches })

elab_rules : command
  | `(declare_writer $n:str touches $ts,*) => addWriter n.getString (ts.getElems.map (·.getString))
  | `(declare_writer $n:str readonly) => addWriter n.getString #[]

/-- Evaluate a `List String` expression at elaboration time. -/
unsafe def evalStringListUnsafe (e : Expr) : MetaM (List String) :=
  evalExpr (List String) (mkApp (mkConst ``List [0]) (mkConst ``String)) e

@[implemented_by evalStringListUnsafe]
opaque evalStringList (e : Expr) : MetaM (List String)

/-- The system `S` of a theorem stating `Invariant S I`, if it does. -/
def invariantSys? (thm : Name) : MetaM (Option Expr) := do
  let ty ← instantiateMVars (← inferType (mkConst thm ((← getConstInfo thm).levelParams.map mkLevelParam)))
  let ty ← whnfR ty
  if ty.isAppOfArity ``Invariant 2 then return some ty.appFn!.appArg! else return none

/-- The writers covered by a proof of `Invariant S I`: `HasWriters.writers S`. -/
def coveredWriters (thm : Name) : MetaM (List String) := do
  let some sys ← invariantSys? thm
    | throwError "register_invariant: `{thm}` does not state `Invariant S I`, so it is not a system \
invariant; list it after one that is, or use `register_property`"
  let inst ← try synthInstance (mkApp (mkConst ``HasWriters) sys)
    catch _ => throwError "register_invariant: no `HasWriters` instance for the system of `{thm}`{indentExpr sys}\n\
Give one, computed from the route table or writer list that defines its `step`."
  evalStringList (← instantiateMVars (mkApp2 (mkConst ``HasWriters.writers) sys inst))

/-- Register a proved system invariant. The first theorem must state
    `Invariant S I`; the writers its proof covers come from `HasWriters S`.
    Other theorems (strengthenings, counterexamples) are supporting evidence;
    any that also state `Invariant _ _` must be about the same `S`.

```
register_invariant "Domain" "Every stored game is `Valid`" by allValid touches "games"
register_invariant "Domain" "…" by allValid touches "games" unproved "adminResetGame"
``` -/
syntax (name := registerInvariant) "register_invariant " str str " by " ident,+
  &" touches " str,+ (&" unproved " str,+)? : command

elab_rules : command
  | `(register_invariant $sec:str $claim:str by $thms,* touches $ts,* $[unproved $un,*]?) => do
    let thms ← thms.getElems.mapM fun id => liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    thms.forM checkEvidenceTheorem
    let touches := ts.getElems.map (·.getString)
    checkTables "register_invariant" touches
    let covers ← liftTermElabM do
      let covers ← coveredWriters thms[0]!
      let some s₀ ← invariantSys? thms[0]! | unreachable!
      for t in thms[1:] do
        if let some s ← invariantSys? t then
          unless ← isDefEq s s₀ do
            throwError "register_invariant: `{t}` is an invariant of a different system than `{thms[0]!}`"
      pure covers
    let unproved := (un.map (·.getElems.map (·.getString))).getD #[]
    for u in unproved do
      unless (allWriters (← getEnv)).any (·.name == u) do
        throwError "register_invariant: `unproved` names `{u}`, which is not a declared writer"
    addProperty { section_ := sec.getString, claim := claim.getString, status := .proved, thms,
                  shape := "system invariant", touches, covers := covers.toArray, unproved }

/-! ## Reports -/

def PropEntry.whereText (e : PropEntry) : String :=
  let base := if e.thms.isEmpty then e.where_
    else ", ".intercalate (e.thms.toList.map fun n => s!"`{n}`")
  if e.unproved.isEmpty then base
  else base ++ s!" (not covering: {", ".intercalate (e.unproved.toList.map fun w => s!"`{w}`")})"

def PropEntry.row (e : PropEntry) : String :=
  let claim := e.claim.replace "|" "\\|"
  s!"| {claim} | **{e.status.label}** | {e.whereText} |"

def sections (es : Array PropEntry) : List String :=
  es.foldl (fun acc e => if acc.contains e.section_ then acc else acc ++ [e.section_]) []

/-- The claim table for one section, as Markdown. -/
def evidenceTable (es : Array PropEntry) (sec : String) : String :=
  let rows := (es.filter (·.section_ == sec)).toList.map PropEntry.row
  "\n".intercalate (["| Claim | Status | Where |", "|---|---|---|"] ++ rows)

/-- Print the registry. -/
elab "#properties" : command => do
  let es := allProperties (← getEnv)
  let lines := es.toList.map fun e =>
    s!"[{e.status.label}] {e.section_}: {e.claim}" ++
      (if e.thms.isEmpty then (if e.where_.isEmpty then "" else s!" ({e.where_})") else s!" ({e.whereText})") ++
      (if e.shape.isEmpty then "" else s!" <{e.shape}>")
  logInfo m!"{es.size} properties\n{"\n".intercalate lines}"

/-- Print every section's claim table between markers, for
    `scripts/gen_evidence.sh`. -/
elab "#evidence_tables" : command => do
  let es := allProperties (← getEnv)
  let out := (sections es).map fun s =>
    s!"<!-- BEGIN GENERATED: {s} -->\n{evidenceTable es s}\n<!-- END GENERATED: {s} -->"
  logInfo ("\n".intercalate out)

/-- The coverage rule (PROPERTIES.md §6.3, union of transitions): every
    writer that touches a table a system invariant is about must be covered
    by the invariant's proof or listed as unproved for it. Also refuses
    covered or unproved names that are not declared writers (drift). -/
def writerCoverageErrors (env : Environment) : List String := Id.run do
  let ws := allWriters env
  let mut errs := []
  for e in allProperties env do
    if e.shape != "system invariant" then continue
    for w in ws do
      if w.touches.any e.touches.contains then
        unless e.covers.contains w.name || e.unproved.contains w.name do
          errs := errs ++ [s!"writer `{w.name}` touches {w.touches.toList} but is not covered by \
the proof of \"{e.claim}\" ({e.whereText}) and is not listed as unproved for it"]
    for c in e.covers ++ e.unproved do
      unless ws.any (·.name == c) do
        errs := errs ++ [s!"\"{e.claim}\" names `{c}`, which is not a declared writer"]
  return errs

elab "#check_writer_coverage" : command => do
  let env ← getEnv
  let errs := writerCoverageErrors env
  unless errs.isEmpty do
    throwError "writer coverage failed:\n{"\n".intercalate errs}"
  let n := (allProperties env).filter (·.shape == "system invariant") |>.size
  logInfo m!"writer coverage: {(allWriters env).size} writers, {n} system invariants, no drift"

end LeanApi.Props
