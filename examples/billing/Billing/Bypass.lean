/-
  Compile-time refusals of the write view, from a *different* module
  so the private constructors of `TxnAs` and `Seen` actually apply.
-/
import Billing.Policies

namespace Billing.Bypass

open LeanDb Billing Billing.Schema Billing.Policies

/-- error: Invalid `⟨...⟩` notation: Constructor for `Billing.Policies.TxnAs` is marked as private -/
#guard_msgs (substring := true) in
def sneakyWrite (p : Tenant) : TxnAs Unit BillingDb p Unit (Option (Stored InvoiceRow)) :=
  ⟨Txn.liftRead (Read.get InvoiceRow ⟨1⟩)⟩

/-- error: Invalid `⟨...⟩` notation: Constructor for `Billing.Policies.Seen` is marked as private -/
#guard_msgs (substring := true) in
def forgedSeen {σ} (p : Tenant) (c : Current σ InvoiceRow) : Seen σ p InvoiceRow :=
  ⟨c⟩

end Billing.Bypass
