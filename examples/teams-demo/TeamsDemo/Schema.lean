/-
  The teams demo's schema: its tables, keys, rules, and who may see what.

  `demo.sh` changes this file one small step at a time, and the compiler
  reports what each change means for the API (README.md).
-/
import LeanDb
import PolicyView.Policy

namespace TeamsDemo

open LeanDb PolicyView

/-! ## Ids -/

structure TeamId where
  n : Nat
  lt : n < 2^63 := by decide
  deriving DecidableEq, Repr

structure UserId where
  n : Nat
  lt : n < 2^63 := by decide
  deriving DecidableEq, Repr

def TeamId.make (n : Nat) : Except String TeamId :=
  if h : n = 0 ∨ n ≥ 2^63 then .error "team id must be between 1 and 2^63-1"
  else .ok ⟨n, by omega⟩

def UserId.make (n : Nat) : Except String UserId :=
  if h : n = 0 ∨ n ≥ 2^63 then .error "user id must be between 1 and 2^63-1"
  else .ok ⟨n, by omega⟩

/-! ## Tables -/

structure TeamRow where
  name : String
  deriving Repr, LeanDb.Entity

structure UserRow where
  email : String
  name : String
  team : Ref TeamRow
  deriving Repr

deriving instance LeanDb.Entity for UserRow

structure TokenRow where
  digest : String
  user : Ref UserRow
  deriving Repr, LeanDb.Entity

/-! ## Keys -/

unique% TokenRow.byDigest := digest

schema% TeamsDb := TeamRow, UserRow, TokenRow

def schema : List TableSpec := IsSchema.specs TeamsDb

/-! ## Ids to references and back -/

def tref (t : TeamId) : Ref TeamRow := ⟨Int64.ofNat t.n⟩
def tid (r : Ref TeamRow) : TeamId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩
def uref (u : UserId) : Ref UserRow := ⟨Int64.ofNat u.n⟩
def uid (r : Ref UserRow) : UserId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩

/-! ## Who may see what -/

/-- The signed-in user. -/
structure Me where
  user : UserId
  team : TeamId

/-- You see the users on your team. (The rule is written twice, once as
    Lean and once as a query that becomes SQL, until `policy%` generates
    both from one lambda: LeanDB M16.) -/
instance : Policy TeamsDb Me UserRow where
  rule me u := u.val.team == tref me.team
  scope me := (Query.from UserRow).where' fun u => u.val.team == tref me.team

end TeamsDemo
