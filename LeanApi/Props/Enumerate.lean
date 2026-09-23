/-
  Small-world enumeration for checking before proving (PLAN.md M10).

  `Enumerate α` lists the "small" values of `α` for a size bound `n`. The
  deriving handler supports structures and non-recursive inductives,
  including proof fields whose statement is decidable (`isLt : i < 9`):
  values are generated field by field and a proof field keeps a candidate
  only when its statement holds.

  Decision 0018 (P3): Plausible builds on toolchain 4.33 but its deriving
  handler rejects proof-carrying fields such as `Cell` and `TimeControl`,
  which are exactly the values the domain uses. We keep this small
  exhaustive generator; exhaustive search also gives a definite "searched
  every world up to size n" instead of a sample.
-/
import Lean

namespace LeanApi.Props

class Enumerate (α : Type) where
  /-- The values of size at most `n` (the meaning of size is per type). -/
  enum : Nat → List α

export Enumerate (enum)

instance : Enumerate Nat := ⟨fun n => List.range (n + 1)⟩
instance : Enumerate Bool := ⟨fun _ => [false, true]⟩
instance : Enumerate Unit := ⟨fun _ => [()]⟩
instance : Enumerate String := ⟨fun n => (List.range (min n 2 + 1)).map fun k => String.ofList (List.replicate k 'a')⟩
instance (k : Nat) : Enumerate (Fin (k + 1)) := ⟨fun n => (List.finRange (k + 1)).take (n + 1)⟩

instance {α : Type} [Enumerate α] : Enumerate (Option α) := ⟨fun n => none :: (enum n).map some⟩

instance {α β : Type} [Enumerate α] [Enumerate β] : Enumerate (α × β) :=
  ⟨fun n => (enum n).flatMap fun a => (enum n).map fun b => (a, b)⟩

instance {α β : Type} [Enumerate α] [Enumerate β] : Enumerate (Sum α β) :=
  ⟨fun n => (enum n).map .inl ++ (enum n).map .inr⟩

/-- Lists of length at most `n` over the values of size at most `n`. -/
def enumLists {α : Type} (xs : List α) : Nat → List (List α)
  | 0 => [[]]
  | k + 1 => [] :: xs.flatMap fun x => (enumLists xs k).map (x :: ·)

instance {α : Type} [Enumerate α] : Enumerate (List α) := ⟨fun n => enumLists (enum n) n⟩

/-! ## Deriving -/

open Lean Elab Command Meta Term

/-- The enumeration term for one constructor. -/
def mkCtorEnum (ctor : Name) (size : Ident) : TermElabM Term := do
  let info ← getConstInfoCtor ctor
  unless info.numParams == 0 do
    throwError "deriving Enumerate: `{info.induct}` has parameters; write the instance by hand"
  forallTelescopeReducing info.type fun xs _ => do
    let names ← xs.mapM fun x => do return mkIdent (← x.fvarId!.getDecl).userName.eraseMacroScopes
    let mut body ← `([$(mkIdent ctor) $names*])
    for i in (List.range xs.size).reverse do
      let x := xs[i]!
      let t ← inferType x
      if (t.find? (·.isConstOf info.induct)).isSome then
        throwError "deriving Enumerate: `{info.induct}` is recursive; write the instance by hand"
      let tStx ← PrettyPrinter.delab t
      if ← isProp t then
        body ← `(dite $tStx (fun $(names[i]!) => $body) (fun _ => []))
      else
        body ← `((LeanApi.Props.Enumerate.enum $size : List $tStx).flatMap fun $(names[i]!) => $body)
    return body

def mkEnumerateInstance (declName : Name) : CommandElabM Unit := do
  let indVal ← getConstInfoInduct declName
  let size := mkIdent `size
  let bodies ← liftTermElabM <| indVal.ctors.mapM fun c => mkCtorEnum c size
  let body ← bodies.foldlM (fun acc b => `($acc ++ $b)) (← `(([] : List $(mkIdent declName))))
  elabCommand (← `(instance : LeanApi.Props.Enumerate $(mkIdent declName) := ⟨fun $size => $body⟩))

def mkEnumerateHandler (declNames : Array Name) : CommandElabM Bool := do
  for n in declNames do
    unless (← getEnv).isConstructor n || (← isInductive n) do return false
    mkEnumerateInstance n
  return true

initialize registerDerivingHandler ``Enumerate mkEnumerateHandler

end LeanApi.Props
