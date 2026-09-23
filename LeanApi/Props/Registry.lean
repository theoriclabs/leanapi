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
  * Writers (routes, jobs, admin commands) and the tables they touch are
    declared with `declare_writer`. `#check_writer_coverage` fails the build
    when a writer touches a table that some registered system invariant is
    about, but is neither covered by that invariant's proof nor listed as
    unproved for it.
-/
import Lean

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
  | `open => pure .open
  | _ => throwErrorAt id "expected a status: proved, checked, assumed or open"

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

/-- Declare a writer (route, job, admin command) and the tables it touches. -/
syntax (name := declareWriter) "declare_writer " str &" touches " str,* : command

elab_rules : command
  | `(declare_writer $n:str touches $ts,*) => do
    let name := n.getString
    if (allWriters (← getEnv)).any (·.name == name) then
      throwError "declare_writer: `{name}` is already declared"
    modifyEnv (writerExt.addEntry · { name, touches := ts.getElems.map (·.getString) })

/-- Evaluate a `List String` term at elaboration time. -/
unsafe def evalStringsUnsafe (t : Term) : TermElabM (List String) := do
  let e ← Term.elabTerm t (some (mkApp (mkConst ``List [0]) (mkConst ``String)))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  evalExpr (List String) (mkApp (mkConst ``List [0]) (mkConst ``String)) e

@[implemented_by evalStringsUnsafe]
opaque evalStrings (t : Term) : TermElabM (List String)

/-- Register a proved system invariant with the writers its proof covers.

```
register_invariant "Domain" "Every stored game is `Valid`" by allValid
  touches "games" covers PrivateGames.Model.provedWriters
```
`covers` is a `List String` term evaluated at build time, so it can be
computed from the same route table the model routes through. -/
syntax (name := registerInvariant) "register_invariant " str str " by " ident,+
  &" touches " str,* &" covers " term (&" unproved " str,*)? : command

elab_rules : command
  | `(register_invariant $sec:str $claim:str by $thms,* touches $ts,* covers $cov $[unproved $un,*]?) => do
    let thms ← thms.getElems.mapM fun id => liftCoreM (realizeGlobalConstNoOverloadWithInfo id)
    thms.forM checkEvidenceTheorem
    let covers ← liftTermElabM (evalStrings cov)
    addProperty { section_ := sec.getString, claim := claim.getString, status := .proved, thms,
                  shape := "system invariant", touches := ts.getElems.map (·.getString),
                  covers := covers.toArray, unproved := (un.map (·.getElems.map (·.getString))).getD #[] }

/-! ## Reports -/

def PropEntry.whereText (e : PropEntry) : String :=
  if e.thms.isEmpty then e.where_
  else ", ".intercalate (e.thms.toList.map fun n => s!"`{n}`")

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
