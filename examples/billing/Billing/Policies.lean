/-
  Row-level policies and a write view for billing.

Who may see or change which rows is declared once per table as a `Policy`
  instance (`rule` plus SQL `scope`). The two fields are written to look
  the same; that they *are* the same is not proved. Default deny. Reads go
  through `PolicyView.ReadAs` or `Scoped`. Writes go through `TxnAs`:
  private constructor, insert/update only with `Owns` evidence, `Seen`
  handles only for rows the actor's policy admits.

  `Auth`'s constructor is still public (PolicyView README); once it is
  private, only authentication can supply the actor.
-/
import PolicyView.Policy
import Billing.Schema

namespace Billing.Policies

open LeanDb PolicyView Billing Billing.Schema LeanApi

/-! ## Policies: one per table, tenant on the row -/

instance : Policy BillingDb Tenant UsageEventRow where
  rule t r := r.val.tenant == tref t.id
  scope t := (LeanDb.Query.from UsageEventRow).where' fun r =>
    r.val.tenant == tref t.id

instance : Policy BillingDb Tenant InvoiceRow where
  rule t r := r.val.tenant == tref t.id
  scope t := (LeanDb.Query.from InvoiceRow).where' fun r =>
    r.val.tenant == tref t.id

/-- `WITH CHECK`: the same rule on the value, without the stored id.
    Our policies do not look at ids, so the two agree. -/
class Owns (s : Type) [IsSchema s] (P : Type) (α : Type) [Entity α] [Policy s P α] where
  owns : P → α → Bool
  owns_eq : ∀ p (r : Stored α), Policy.rule (s := s) p r = owns p r.val

instance : Owns BillingDb Tenant UsageEventRow where
  owns t v := v.tenant == tref t.id
  owns_eq _ _ := rfl

instance : Owns BillingDb Tenant InvoiceRow where
  owns t v := v.tenant == tref t.id
  owns_eq _ _ := rfl

/-- Domain ownership through the row mapping: `Policy.rule` (and `Owns`)
    hold of a stored event iff the event's tenant is the actor. The SQL
    `scope` field is written to look the same; that it *is* the same is
    not proved (`policy%` / LeanDB view laws). -/
theorem usage_owns_iff (p : Tenant) (e : UsageEvent) :
    Owns.owns (s := BillingDb) p (UsageEventRow.ofEvent e) = true ↔ e.tenant = p.id := by
  simp [Owns.owns, UsageEventRow.ofEvent, ref_beq_eq, tref_eq_iff]

theorem usage_rule_ofEvent (p : Tenant) (id : LeanDb.Id UsageEventRow) (e : UsageEvent) :
    Policy.rule (s := BillingDb) p ⟨id, UsageEventRow.ofEvent e⟩ = true ↔
      e.tenant = p.id := by
  rw [Owns.owns_eq (s := BillingDb) p ⟨id, UsageEventRow.ofEvent e⟩]
  exact usage_owns_iff p e

theorem invoice_owns_iff (p : Tenant) (inv : Invoice) :
    Owns.owns (s := BillingDb) p (InvoiceRow.ofInvoice inv) = true ↔
      inv.tenant = p.id := by
  simp [Owns.owns, InvoiceRow.ofInvoice, ref_beq_eq, tref_eq_iff]

theorem invoice_rule_ofInvoice (p : Tenant) (id : LeanDb.Id InvoiceRow) (inv : Invoice) :
    Policy.rule (s := BillingDb) p ⟨id, InvoiceRow.ofInvoice inv⟩ = true ↔
      inv.tenant = p.id := by
  rw [Owns.owns_eq (s := BillingDb) p ⟨id, InvoiceRow.ofInvoice inv⟩]
  exact invoice_owns_iff p inv

/-! ## Scoped reads that can add filters (policy + predicate in SQL) -/

def Scoped.all (α : Type) [Entity α] [Policy BillingDb Tenant α] (p : Tenant) :
    Read BillingDb (List (Stored α)) :=
  Read.all (Policy.scope (s := BillingDb) p)

def Scoped.get (α : Type) [Entity α] [Policy BillingDb Tenant α] (p : Tenant)
    (id : LeanDb.Id α) : Read BillingDb (Option (Stored α)) :=
  (·.head?) <$> Read.all ((Policy.scope (s := BillingDb) p).where' fun r => r.id == id)

def Scoped.where (α : Type) [Entity α] [Policy BillingDb Tenant α] (p : Tenant)
    (pred : Stored α → Bool) : Read BillingDb (List (Stored α)) :=
  Read.all ((Policy.scope (s := BillingDb) p).where' pred)

/-! ## Write view: private constructor, owned rows only -/

/-- A row this transaction has seen through the actor's policy. -/
structure Seen (σ : Type) {P : Type} (p : P) (α : Type) [Entity α] where
  private mk ::
  cur : Current σ α

namespace Seen
variable {σ : Type} {P : Type} {p : P} {α : Type} [Entity α]
def id (s : Seen σ p α) : LeanDb.Id α := s.cur.id
def val (s : Seen σ p α) : α := s.cur.val
def toStored (s : Seen σ p α) : Stored α := s.cur.toStored
end Seen

/-- A transaction program over the database as `p` sees it. -/
structure TxnAs (σ s : Type) [IsSchema s] {P : Type} (p : P) (ε α : Type) : Type 1 where
  private mk ::
  prog : Txn σ s ε α

namespace TxnAs
variable {σ s : Type} [IsSchema s] {P : Type} {p : P} {ε : Type}

instance : Monad (TxnAs σ s p ε) where
  pure a := ⟨pure a⟩
  bind m f := ⟨m.prog >>= fun a => (f a).prog⟩

def throw (e : ε) : TxnAs σ s p ε α := ⟨Txn.throw e⟩

/-- Every visible row of `α`. No policy, no read. -/
def all (α : Type) [Entity α] [Policy s P α] : TxnAs σ s p ε (List (Stored α)) :=
  ⟨Txn.liftRead (Read.all (Policy.scope (s := s) p))⟩

/-- The row with this id, if `p` may see it. Policy and id go to SQL. -/
def get (α : Type) [Entity α] [Policy s P α] (id : LeanDb.Id α) :
    TxnAs σ s p ε (Option (Seen σ p α)) :=
  ⟨do
    match ← Txn.liftRead (Read.all ((Policy.scope (s := s) p).where' fun r => r.id == id)) with
    | [] => pure none
    | s :: _ =>
      match ← Txn.get α s.id with
      | none => pure none
      | some c => pure (some ⟨c⟩)⟩

/-- Insert a row this actor owns (`WITH CHECK`). -/
def insert (α : Type) [Entity α] [HasUnique α] [HasForeignKey α] [Policy s P α] [Owns s P α]
    (v : Checked α) (_h : Owns.owns (s := s) p v.val = true) :
    TxnAs σ s p ε (Except (InsertError α) (Seen σ p α)) :=
  ⟨do
    match ← Txn.insert α v with
    | .error e => pure (.error e)
    | .ok c => pure (.ok ⟨c⟩)⟩

/-- Replace a row this transaction read through the view, if the new
    value is still owned (`WITH CHECK`). -/
def update (α : Type) [Entity α] [HasUnique α] [HasForeignKey α] [Policy s P α] [Owns s P α]
    (row : Seen σ p α) (new : Checked α) (_h : Owns.owns (s := s) p new.val = true) :
    TxnAs σ s p ε (Except (UpdateError α) (Stored α)) :=
  ⟨Txn.update α row.toStored new⟩

end TxnAs

/-- Rank-2 write program: `Current` / `Seen` cannot escape. -/
abbrev WriteAs (s : Type) [IsSchema s] {P : Type} (p : P) (ε ρ : Type) :=
  {σ : Type} → TxnAs σ s p ε ρ

def WriteAs.toTx {s : Type} [IsSchema s] {P : Type} {p : P} {ε ρ : Type}
    (w : WriteAs s p ε ρ) : Tx s ε ρ :=
  fun {σ} => (w (σ := σ)).prog

/-! ## Projection: the invoice a tenant sees -/

structure LineView where
  eventId : EventId
  quantity : Quantity
  unitPriceMinor : Nat
  amountMinor : Nat

structure InvoiceView where
  id : InvoiceId
  period : Period
  lines : List LineView
  totalMinor : Nat
  currency : Currency
  status : Status

structure UsageView where
  eventId : EventId
  quantity : Quantity
  occurredAt : Instant
  period : Period

def lineView (l : Line) : LineView :=
  ⟨l.eventId, l.quantity, l.unitPrice.minor, l.amount.minor⟩

def projectInvoice (id : InvoiceId) (inv : Invoice) : InvoiceView :=
  { id, period := inv.period, lines := inv.lines.map lineView,
    totalMinor := inv.total.minor, currency := .usd, status := inv.status }

def projectUsage (e : UsageEvent) : UsageView :=
  ⟨e.eventId, e.quantity, e.occurredAt, e.period⟩

/-- SQL filter a scoped get of an invoice sends (for display). -/
def invoiceGetSql (p : Tenant) (id : LeanDb.Id InvoiceRow) : String × Array Col :=
  ((Policy.scope (s := BillingDb) p).where' fun (r : Stored InvoiceRow) => r.id == id).pred.renderT

/-! ## What the view refuses, at compile time

Bypasses of `TxnAs` / `Seen` are in `Billing.Bypass`: those constructors
are private to this module, so they have to be refused from outside. -/

/-- error: failed to synthesize instance of type class
  Policy BillingDb Tenant TenantRow -/
#guard_msgs (substring := true) in
def sneakTenants (me : Actor Tenant) : ReadAs BillingDb me (List (Stored TenantRow)) :=
  ReadAs.all TenantRow

/-- error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.Actor` is marked as private -/
#guard_msgs (substring := true) in
def spoofActor (id : LeanDb.Id InvoiceRow) :
    ReadAs BillingDb (⟨{ id := ⟨1⟩, unitPrice := ⟨0, by decide⟩ }⟩ : Actor Tenant)
      (Option (Stored InvoiceRow)) :=
  ReadAs.get InvoiceRow id

end Billing.Policies
