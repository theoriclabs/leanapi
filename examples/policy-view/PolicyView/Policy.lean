/-
  Row-level security as a LeanDB view: the framework half.
  A prototype of DESIGN.md §7.5, built on LeanDB as it is (no LeanDB
  changes). See README.md next to this directory for what it enforces and
  what it does not yet.
-/
import LeanDb
import LeanApi
open LeanDb

namespace PolicyView

/-- A row-level policy: which rows of `α` the actor `p : P` may see in
    schema `s`. Declared once per table. `policy%` would generate this
    instance from one lambda, so the two fields are the same rule. -/
class Policy (s : Type) [IsSchema s] (P : Type) (α : Type) [Entity α] where
  /-- The rule as a Lean function: the meaning, what proofs talk about. -/
  rule : P → Stored α → Bool
  /-- The same rule as a query, which LeanDB compiles to SQL. -/
  scope : P → Query s [α] (Stored α)

/-- An authenticated actor. The constructor is private: application code
    cannot make one, so it cannot act as someone else. -/
structure Actor (P : Type) where
  private mk ::
  val : P

/-- A read program over the database *as `me` sees it*. The constructor is
    private: the only way to build one is through the scoped operations
    below, so an unscoped `Read` cannot be smuggled in. -/
structure ReadAs (s : Type) [IsSchema s] {P : Type} (me : Actor P) (α : Type) : Type 1 where
  private mk ::
  prog : Read s α

namespace ReadAs
variable {s : Type} [IsSchema s] {P : Type} {me : Actor P}

instance : Monad (ReadAs s me) where
  pure a := ⟨pure a⟩
  bind m f := ⟨m.prog >>= fun a => (f a).prog⟩

/-- Every row of `α` that `me` may see. No policy for `α`, no read. -/
def all (α : Type) [Entity α] [Policy s P α] : ReadAs s me (List (Stored α)) :=
  ⟨Read.all (Policy.scope me.val)⟩

/-- The row with this id, if `me` may see it: the policy and the id go to
    SQL together, so another player's row is never fetched. -/
def get (α : Type) [Entity α] [Policy s P α] (id : LeanDb.Id α) : ReadAs s me (Option (Stored α)) :=
  ⟨(·.head?) <$> Read.all ((Policy.scope (s := s) me.val).where' fun r => r.id == id)⟩

/-- The SQL filter a scoped `get` sends (for display). -/
def getSql (α : Type) [Entity α] [Policy s P α] (p : P) (id : LeanDb.Id α) : String × Array Col :=
  ((Policy.scope (s := s) p).where' fun (r : Stored α) => r.id == id).pred.renderT

end ReadAs

/-- Bridge for `DbApi` handlers today: the scoped program for the request's
    authenticated actor, as the `Read` a handler returns. `Auth`'s
    constructor is private (`LeanApi/Http/Endpoint.lean`), so only
    authentication supplies `me`: an application cannot forge one. -/
def ReadAs.forAuth {s : Type} [IsSchema s] {P α : Type} (me : LeanApi.Auth P)
    (prog : (a : Actor P) → ReadAs s a α) : Read s α :=
  (prog ⟨me.val⟩).prog

/-- The framework: authentication has produced `p`; run the handler's
    program over `p`'s view. Only this module can make the `Actor`. -/
def runAs {s : Type} [IsSchema s] {P α : Type} (conn : Conn) (p : P)
    (handler : (me : Actor P) → ReadAs s me α) : IO (Except DbError (Except DbFault α)) :=
  DbM.run conn (Read.run (handler ⟨p⟩).prog)

end PolicyView
