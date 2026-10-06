import LeanApi.Core.Flow
import Lean.Elab.Tactic.Basic

/-! # Operations as ordinary Lean

`Op ε α` (read-write) and `ReadOp ε α` (read-only) are `Flow` at the portable family and the
model transaction index `OpScope`. There is one semantics: `Flow.run`. A `DB` step (LeanDB)
lifts into `Op`, a `Query` step into `ReadOp` and `Op`, request by request, through
`MonadStorage` (`LeanDb.Model.Program.lift`); the storage request is embedded unchanged.

Publication (`LeanApi.Core.Publish`) abstracts the portable family, its named instances and
`OpScope` out of an operation's elaborated body, which yields the resource-generic,
Scope-polymorphic `bodyWithResources` a native adapter runs. -/

namespace LeanApi.Core
open Ontology LeanDb.Model

/-- The server's clock reading. Only `Clock.now` (or an explicitly trusted adapter) can
produce one, so a rule or write that takes `Now` cannot be fed a time from the request
(coordination decision 14). It coerces to `Time`, so `now < p.date` elaborates. -/
structure Now where
  private mk ::
  time : Time

instance : Coe Now Time := ⟨Now.time⟩

/-- Trusted assembly/test boundary: a `Now` from an externally sampled clock. -/
def Trusted.now (time : Time) : Now := ⟨time⟩

/-- A read-write operation: one writer transaction; it returns `α` or fails with the
authored domain error `ε`. -/
def Op (ε α : Type) : Type 1 := Flow .command OpScope ε α
/-- A read-only operation over one snapshot; it lifts into `Op`. -/
def ReadOp (ε α : Type) : Type 1 := Flow .query OpScope ε α

instance : Monad (Op ε) := inferInstanceAs (Monad (FlowF portableResources .command OpScope ε))
instance : Monad (ReadOp ε) := inferInstanceAs (Monad (FlowF portableResources .query OpScope ε))

instance : MonadExceptOf ε (Op ε) where
  throw := Flow.fail
  tryCatch := Flow.tryCatch
instance : MonadExceptOf ε (ReadOp ε) where
  throw := Flow.fail
  tryCatch := Flow.tryCatch

/- LeanDB's storage programs embed request by request: `MonadStorage` gives
`MonadLift DB (Op ε)`, `MonadLift Query (Op ε)` and `MonadLift Query (ReadOp ε)`. -/
instance storageOp : MonadStorage portableStorage .command OpScope (Op ε) where
  storage request := Flow.request (RequestF.storage (kind := .command) request)
instance storageOpQuery : MonadStorage portableStorage .query OpScope (Op ε) where
  storage request := Flow.request (RequestF.storage (kind := .command) request.toCommand)
instance storageReadOp : MonadStorage portableStorage .query OpScope (ReadOp ε) where
  storage request := Flow.request (RequestF.storage (kind := .query) request)

instance : MonadLift (ReadOp ε) (Op ε) := ⟨Flow.toCommand⟩

/-- Call another operation with a different closed error type: every alternative must be
mapped, so a new case in the callee breaks the caller until handled. -/
def Op.mapError (f : ε → δ) (op : Op ε α) : Op δ α := Flow.mapError f op
def ReadOp.mapError (f : ε → δ) (op : ReadOp ε α) : ReadOp δ α := Flow.mapError f op

instance : Inhabited (Op ε Unit) := ⟨Flow.pure ()⟩
instance : Inhabited (ReadOp ε Unit) := ⟨Flow.pure ()⟩

/-- Check a decidable proposition; hand back its proof, or fail the operation with `err`.
`let ⟨h⟩ ← require p .err` binds `h : p`. -/
def «require» (p : Prop) [Decidable p] (err : ε) : Op ε (PLift p) := Flow.check p inferInstance err
/-- `require` inside a read-only operation. -/
def ReadOp.«require» (p : Prop) [Decidable p] (err : ε) : ReadOp ε (PLift p) := Flow.check p inferInstance err

/-- Server time, sampled by the runtime when the request is interpreted (after writer
admission for `Op`). Never part of the request. -/
def Clock.now : Op ε Now := Flow.bind (Flow.request .now) fun time => Flow.pure ⟨time⟩
/-- Snapshot time inside a read-only operation. -/
def ReadOp.now : ReadOp ε Now := Flow.bind (Flow.request .now) fun time => Flow.pure ⟨time⟩

/-- Lets the `require p err` surface work in both `Op` and `ReadOp` do-blocks. -/
class MonadRequire (ε : outParam Type) (m : Type → Type 1) where
  requireWith : (p : Prop) → Decidable p → ε → m (PLift p)
instance : MonadRequire ε (Op ε) := ⟨fun p decision err => @«require» ε p decision err⟩
instance : MonadRequire ε (ReadOp ε) := ⟨fun p decision err => @ReadOp.«require» ε p decision err⟩

/-- `Decidable p`, unfolding definitions such as `def MayEdit … : Prop := …` as needed. -/
partial def decidableByUnfolding (p : Lean.Expr) : Lean.MetaM Lean.Expr := do
  match ← Lean.Meta.synthInstance? (Lean.mkApp (Lean.mkConst ``Decidable) p) with
  | some inst => return inst
  | none =>
    match ← Lean.Meta.unfoldDefinition? p with
    | some unfolded => decidableByUnfolding unfolded
    | none =>
      let whnf ← Lean.Meta.whnfR p
      if whnf != p then decidableByUnfolding whnf
      else Lean.throwError m!"require: failed to find a Decidable instance for{Lean.indentExpr p}"

/-- Closes `Decidable p` goals, unfolding the proposition's head definitions. -/
elab "domain_decidable" : tactic => Lean.Elab.Tactic.liftMetaTactic fun goal => do
  let goalType ← Lean.instantiateMVars (← goal.getType)
  let some p := goalType.app1? ``Decidable | Lean.throwError "domain_decidable: expected a Decidable goal"
  goal.assign (← decidableByUnfolding p)
  return []

/-- Types the runtime may fill from a verified session (an app's own `SignedIn`, declared
with `deriving Principal`). A published operation's parameter of a `Principal` type (or
`Option` of one) is the actor, never request input. -/
class Principal (A : Type) where
  Profile : Type
  id : A → Ref Profile
  /-- Trusted adapter construction from a live profile row. Assembly only. -/
  trusted : Ref Profile → Profile → A

/-- `Op Empty α` publishes with an empty error schema. -/
instance : HasTypeId Empty := ⟨{ packageName := "lean", name := "Empty" }⟩
instance : Domain Empty := { typeId := { packageName := "lean", name := "Empty" }, cases := [] }
instance : Wire Empty := ⟨enumCodec { packageName := "lean", name := "Empty" } [] (fun value => nomatch value)⟩

/-- `require p err` in `Op`/`ReadOp`; decides `p` by unfolding authored rule definitions. -/
scoped syntax (name := requireTerm) "require " term:max term:max : term
macro_rules (kind := requireTerm)
  | `(require $p $err) => `(LeanApi.Core.MonadRequire.requireWith $p (by first | infer_instance | domain_decidable) $err)

end LeanApi.Core
