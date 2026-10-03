import LeanApiDomain.Contract
import LeanApp.Domain.Flow

/-! Native execution of the portable interpreter. Schema/evidence derivation supplies
an algebra; this module does not dispatch by string or duplicate any flow body. -/
namespace LeanApi.Domain
open LeanDb LeanApp.Domain

/-- Authentication and policy/data interpretation share a single read program. -/
def queryFlowWithResources {s : Type} [IsSchema s] {resources : ResourceFamily}
    (operation : LeanApp.Domain.Operation .query Actor Input Output Error)
    (requirements : operation.Requirements resources)
    (resolve : LeanApi.Env → LeanApi.Req → Read s (Contract.CallResult (Actor Unit) Error))
    (algebra : LeanApi.Env → Algebra (Read s) .query Unit Error resources)
    (env : LeanApi.Env) (req : LeanApi.Req) (input : Input) :
    Read s (Contract.CallResult Output Error) :=
  Read.bind (resolve env req) fun
    | .error error => Read.pure (.error error)
    | .ok actor => Read.bind (Flow.run (algebra env) (operation.bodyWithResources requirements actor input))
        (fun result => Read.pure (result.mapError Contract.CallError.domain))

/-- Portable specialization; native generated assembly uses the witnessed entry point. -/
def queryFlow {s : Type} [IsSchema s]
    (operation : LeanApp.Domain.Operation .query Actor Input Output Error)
    (resolve : LeanApi.Env → LeanApi.Req → Read s (Contract.CallResult (Actor Unit) Error))
    (algebra : LeanApi.Env → Algebra (Read s) .query Unit Error)
    (env : LeanApi.Env) (req : LeanApi.Req) (input : Input) :
    Read s (Contract.CallResult Output Error) :=
  queryFlowWithResources operation operation.portable resolve algebra env req input

/-- Native checked identities can fail in a framework channel without extending
the generated closed domain Error. The shared interpreter still owns flow order. -/
def queryFlowCheckedWithResources {s : Type} [IsSchema s] {resources : ResourceFamily}
    (operation : LeanApp.Domain.Operation .query Actor Input Output Error)
    (requirements : operation.Requirements resources)
    (resolve : LeanApi.Env → LeanApi.Req → Read s (Contract.CallResult (Actor Unit) Error))
    (algebra : LeanApi.Env →
      Algebra (ExceptT (Contract.CallError Error) (Read s)) .query Unit Error resources)
    (env : LeanApi.Env) (req : LeanApi.Req) (input : Input) :
    Read s (Contract.CallResult Output Error) := do
  match ← resolve env req with
  | .error error => return .error error
  | .ok actor =>
    match ← (Flow.run (algebra env) (operation.bodyWithResources requirements actor input)).run with
    | .error error => return .error error
    | .ok result => return result.mapError Contract.CallError.domain

/-- A late flow failure is an abort, including a guard after earlier writes. The Scope
is exactly the enclosing native transaction index. Actor resolution is inside it. -/
def commandFlowWithResources {s : Type} [IsSchema s] {resources : ResourceFamily}
    (operation : LeanApp.Domain.Operation .command Actor Input Output Error)
    (requirements : operation.Requirements resources)
    (resolve : {Scope : Type} → LeanApi.Env → LeanApi.Req →
      Txn Scope s (Contract.CallError Error) (Actor Scope))
    (algebra : {Scope : Type} → LeanApi.Env →
      Algebra (Txn Scope s (Contract.CallError Error)) .command Scope Error resources)
    (env : LeanApi.Env) (req : LeanApi.Req) (input : Input) :
    {Scope : Type} → Txn Scope s (Contract.CallError Error) Output := do
  let actor ← resolve env req
  match ← Flow.run (algebra env) (operation.bodyWithResources requirements actor input) with
  | .ok output => pure output
  | .error error => Txn.throw (.domain error)

def commandFlow {s : Type} [IsSchema s]
    (operation : LeanApp.Domain.Operation .command Actor Input Output Error)
    (resolve : {Scope : Type} → LeanApi.Env → LeanApi.Req →
      Txn Scope s (Contract.CallError Error) (Actor Scope))
    (algebra : {Scope : Type} → LeanApi.Env →
      Algebra (Txn Scope s (Contract.CallError Error)) .command Scope Error)
    (env : LeanApi.Env) (req : LeanApi.Req) (input : Input) :
    {Scope : Type} → Txn Scope s (Contract.CallError Error) Output :=
  commandFlowWithResources operation operation.portable resolve algebra env req input

/-- Native requirements retain actual backend dictionaries through the shared flow. -/
def publishQueryWithResources {s : Type} [IsSchema s] {resources : ResourceFamily}
    (codecs : Contract.Http.Codecs)
    (operation : LeanApp.Domain.Operation .query Actor Input Output Error)
    (requirements : operation.Requirements resources)
    (resolve : LeanApi.Env → LeanApi.Req → Read s (Contract.CallResult (Actor Unit) Error))
    (algebra : LeanApi.Env → Algebra (Read s) .query Unit Error resources)
    (status : Error → Nat) (http : LeanApp.HttpBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  TrustedAdapter.query codecs operation.contract
    (queryFlowWithResources operation requirements resolve algebra) status http metadata

def publishQueryCheckedWithResources {s : Type} [IsSchema s] {resources : ResourceFamily}
    (codecs : Contract.Http.Codecs)
    (operation : LeanApp.Domain.Operation .query Actor Input Output Error)
    (requirements : operation.Requirements resources)
    (resolve : LeanApi.Env → LeanApi.Req → Read s (Contract.CallResult (Actor Unit) Error))
    (algebra : LeanApi.Env →
      Algebra (ExceptT (Contract.CallError Error) (Read s)) .query Unit Error resources)
    (status : Error → Nat) (http : LeanApp.HttpBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  TrustedAdapter.query codecs operation.contract
    (queryFlowCheckedWithResources operation requirements resolve algebra) status http metadata

def publishCommandWithResources {s : Type} [IsSchema s] {resources : ResourceFamily}
    (codecs : Contract.Http.Codecs)
    (operation : LeanApp.Domain.Operation .command Actor Input Output Error)
    (requirements : operation.Requirements resources)
    (resolve : {Scope : Type} → LeanApi.Env → LeanApi.Req →
      Txn Scope s (Contract.CallError Error) (Actor Scope))
    (algebra : {Scope : Type} → LeanApi.Env →
      Algebra (Txn Scope s (Contract.CallError Error)) .command Scope Error resources)
    (status : Error → Nat) (http : LeanApp.HttpBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  TrustedAdapter.command codecs operation.contract
    (commandFlowWithResources operation requirements resolve algebra) status http metadata

/-- Explicit-route publication of a checked query (`RouteBinding`, e.g. a GET template). -/
def publishQueryCheckedWithResourcesAt {s : Type} [IsSchema s] {resources : ResourceFamily}
    (codecs : Contract.Http.Codecs)
    (operation : LeanApp.Domain.Operation .query Actor Input Output Error)
    (requirements : operation.Requirements resources)
    (resolve : LeanApi.Env → LeanApi.Req → Read s (Contract.CallResult (Actor Unit) Error))
    (algebra : LeanApi.Env →
      Algebra (ExceptT (Contract.CallError Error) (Read s)) .query Unit Error resources)
    (status : Error → Nat) (binding : RouteBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  TrustedAdapter.queryAt codecs operation.contract
    (queryFlowCheckedWithResources operation requirements resolve algebra) status binding metadata

/-- Explicit-route publication of a command (`RouteBinding`, e.g. a POST template). -/
def publishCommandWithResourcesAt {s : Type} [IsSchema s] {resources : ResourceFamily}
    (codecs : Contract.Http.Codecs)
    (operation : LeanApp.Domain.Operation .command Actor Input Output Error)
    (requirements : operation.Requirements resources)
    (resolve : {Scope : Type} → LeanApi.Env → LeanApi.Req →
      Txn Scope s (Contract.CallError Error) (Actor Scope))
    (algebra : {Scope : Type} → LeanApi.Env →
      Algebra (Txn Scope s (Contract.CallError Error)) .command Scope Error resources)
    (status : Error → Nat) (binding : RouteBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  TrustedAdapter.commandAt codecs operation.contract
    (commandFlowWithResources operation requirements resolve algebra) status binding metadata

/-- Derivation-facing publication; status/input/output/error identity stays typed. -/
def publishQuery {s : Type} [IsSchema s] (codecs : Contract.Http.Codecs)
    (operation : LeanApp.Domain.Operation .query Actor Input Output Error)
    (resolve : LeanApi.Env → LeanApi.Req → Read s (Contract.CallResult (Actor Unit) Error))
    (algebra : LeanApi.Env → Algebra (Read s) .query Unit Error)
    (status : Error → Nat) (http : LeanApp.HttpBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  publishQueryWithResources codecs operation operation.portable resolve algebra status http metadata

def publishCommand {s : Type} [IsSchema s] (codecs : Contract.Http.Codecs)
    (operation : LeanApp.Domain.Operation .command Actor Input Output Error)
    (resolve : {Scope : Type} → LeanApi.Env → LeanApi.Req →
      Txn Scope s (Contract.CallError Error) (Actor Scope))
    (algebra : {Scope : Type} → LeanApi.Env →
      Algebra (Txn Scope s (Contract.CallError Error)) .command Scope Error)
    (status : Error → Nat) (http : LeanApp.HttpBinding)
    (metadata : LeanApp.PublicMetadata := {}) : Published s :=
  publishCommandWithResources codecs operation operation.portable resolve algebra status http metadata

theorem queryFlowWithResources_denote {s : Type} [IsSchema s] {resources : ResourceFamily}
    (operation : LeanApp.Domain.Operation .query Actor Input Output Error)
    (requirements : operation.Requirements resources)
    (resolve : LeanApi.Env → LeanApi.Req → Read s (Contract.CallResult (Actor Unit) Error))
    (algebra : LeanApi.Env → Algebra (Read s) .query Unit Error resources)
    (env : LeanApi.Env) (req : LeanApi.Req) (input : Input) (state : DbState s) :
    Read.denote (queryFlowWithResources operation requirements resolve algebra env req input) state =
      match Read.denote (resolve env req) state with
      | .error error => .error error
      | .ok actor => (Read.denote (Flow.run (algebra env)
          (operation.bodyWithResources requirements actor input)) state).mapError Contract.CallError.domain := by
  simp only [queryFlowWithResources, Read.denote]
  cases Read.denote (resolve env req) state <;> simp only [Read.denote]

/-- A resolved query denotes exactly the shared flow interpreter, with the framework
and domain channels kept separate. No engine correspondence assumption is hidden here. -/
theorem queryFlow_denote {s : Type} [IsSchema s]
    (operation : LeanApp.Domain.Operation .query Actor Input Output Error)
    (resolve : LeanApi.Env → LeanApi.Req → Read s (Contract.CallResult (Actor Unit) Error))
    (algebra : LeanApi.Env → Algebra (Read s) .query Unit Error)
    (env : LeanApi.Env) (req : LeanApi.Req) (input : Input) (state : DbState s) :
    Read.denote (queryFlow operation resolve algebra env req input) state =
      match Read.denote (resolve env req) state with
      | .error error => .error error
      | .ok actor => (Read.denote (Flow.run (algebra env) (operation.body actor input)) state).mapError
          Contract.CallError.domain := by
  exact queryFlowWithResources_denote operation operation.portable resolve algebra env req input state

private theorem go_abort_restores {s Scope Error Output : Type} [IsSchema s]
    (program : Txn Scope s Error Output) (initial : DbState s) :
    ∀ state error, (Txn.denote.go initial program state).1 = .error error →
      (Txn.denote.go initial program state).2 = initial := by
  induction program with
  | bind m f ihm ihf =>
    intro state error failed
    simp only [Txn.denote.go] at failed ⊢
    cases h : Txn.denote.go initial m state with
    | mk result next =>
      cases result with
      | error e =>
        simp only [h] at failed ⊢
        simpa only [h] using ihm state e (by rw [h])
      | ok value =>
        simp only [h] at failed ⊢
        exact ihf value next error failed
  | orAbort m f ih =>
    intro state error failed
    simp only [Txn.denote.go] at failed ⊢
    cases h : Txn.denote.go initial m state with
    | mk result next =>
      cases result with
      | error e =>
        simp only [h] at failed ⊢
        simpa only [h] using ih state e (by rw [h])
      | ok value =>
        cases value <;> simp [h] at failed ⊢
  | orElse m f ihm ihf =>
    intro state error failed
    simp only [Txn.denote.go] at failed ⊢
    cases h : Txn.denote.go initial m state with
    | mk result next =>
      cases result with
      | error e =>
        simp only [h] at failed ⊢
        simpa only [h] using ihm state e (by rw [h])
      | ok value =>
        cases value with
        | error e =>
          simp only [h] at failed ⊢
          exact ihf e next error failed
        | ok value => simp [h] at failed
  | throw e => intros; rfl
  | _ =>
    intro state error failed
    simp only [Txn.denote.go] at failed
    (repeat' split at failed) <;> cases failed

/-- All native aborts restore the complete schema state, including failures after writes.
This is a law of the actual program meaning, independent of SQLite/FFI claims. -/
theorem transaction_abort_restores {s Scope Error Output : Type} [IsSchema s]
    (program : Txn Scope s Error Output) (state : DbState s) (error : Error)
    (failed : (Txn.denote program state).1 = .error error) :
    (Txn.denote program state).2 = state :=
  go_abort_restores program state state error failed

end LeanApi.Domain
