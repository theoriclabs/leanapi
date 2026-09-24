/-
  LeanDB mapping for usage-based billing.

  Column codecs go through the same smart constructors the HTTP
  extractors use, so storage cannot hold a value the API would reject.

  Tables:
    tenant        API key, unit price (USD cents)
    usage_event   tenant, event id (unique together), quantity, instant, period
    invoice       tenant, period (unique together), total, status, lines (child list)

  The invoice invariant is the domain's `Balanced`. `Checked` rows are
  built from domain proofs, with no runtime recomputation of the total.
-/
import LeanDb
import Billing.Domain

namespace Billing.Schema

open LeanDb Billing

/-! ## Closed enums and codecs -/

inductive RowStatus where
  | draft | finalized | paid | void
  deriving Repr, DecidableEq, LeanDb.ClosedEnum

def RowStatus.toDomain : RowStatus → Status
  | .draft => .draft
  | .finalized => .sealed .finalized
  | .paid => .sealed .paid
  | .void => .sealed .void

def RowStatus.ofStatus : Status → RowStatus
  | .draft => .draft
  | .sealed .finalized => .finalized
  | .sealed .paid => .paid
  | .sealed .void => .void

theorem RowStatus.toDomain_ofStatus (s : Status) : (RowStatus.ofStatus s).toDomain = s := by
  cases s with
  | draft => rfl
  | sealed t => cases t <;> rfl

deriving instance LeanDb.ClosedEnum for Currency

instance : ColCodec EventId := ColCodec.via (β := String) (·.raw) EventId.make
instance : ColCodec Quantity := ColCodec.via (β := Nat) (·.n) Quantity.make
instance : ColCodec Instant := ColCodec.via (β := Nat) (·.unixSec) Instant.make
instance : ColCodec (Money .usd) := ColCodec.via (β := Nat) (·.minor) (Money.make .usd)
instance : ColCodec (UnitPrice .usd) := ColCodec.via (β := Nat) (·.minor) (UnitPrice.make .usd)
instance : ColCodec ApiKey := ColCodec.via (β := String) (·.raw) ApiKey.make

theorem nat_roundtrip (n : Nat) (h : n < 2 ^ 63) :
    (ColCodec.fromCol (ColCodec.toCol n) : Except String Nat) = .ok n := by
  have h1 : ¬ (Int64.ofNat n < 0) := by
    rw [Int64.lt_iff_toInt_lt]; simp [Int64.toInt_ofNat_of_lt h]
  have hmax : LeanDb.natSqlMax = 2 ^ 63 - 1 := by decide
  have hs : LeanDb.natToSql n = some (Int64.ofNat n) := by
    simp only [LeanDb.natToSql, hmax]; split <;> first | rfl | omega
  simp [ColCodec.fromCol, ColCodec.toCol, hs, h1, Int64.toNatClampNeg_ofNat_of_lt h]

theorem quantity_roundtrip (q : Quantity) :
    (ColCodec.fromCol (ColCodec.toCol q) : Except String Quantity) = .ok q := by
  show (do Quantity.make (← (ColCodec.fromCol (ColCodec.toCol q.n) : Except String Nat))) = .ok q
  rw [nat_roundtrip q.n q.lt]
  exact Quantity.make_n q

theorem instant_roundtrip (t : Instant) :
    (ColCodec.fromCol (ColCodec.toCol t) : Except String Instant) = .ok t := by
  show (do Instant.make (← (ColCodec.fromCol (ColCodec.toCol t.unixSec) : Except String Nat))) = .ok t
  rw [nat_roundtrip t.unixSec t.lt]
  exact Instant.make_unixSec t

theorem eventId_roundtrip (e : EventId) :
    (ColCodec.fromCol (ColCodec.toCol e) : Except String EventId) = .ok e := by
  show (do EventId.make (← (ColCodec.fromCol (ColCodec.toCol e.raw) : Except String String))) = .ok e
  have hs : (ColCodec.fromCol (ColCodec.toCol e.raw) : Except String String) = .ok e.raw := rfl
  rw [hs]; exact EventId.make_raw e

theorem money_roundtrip (m : Money .usd) :
    (ColCodec.fromCol (ColCodec.toCol m) : Except String (Money .usd)) = .ok m := by
  show (do Money.make .usd (← (ColCodec.fromCol (ColCodec.toCol m.minor) : Except String Nat))) = .ok m
  rw [nat_roundtrip m.minor m.lt]
  simp only [bind, Except.bind]
  exact Money.make_minor m

theorem unitPrice_roundtrip (p : UnitPrice .usd) :
    (ColCodec.fromCol (ColCodec.toCol p) : Except String (UnitPrice .usd)) = .ok p := by
  show (do UnitPrice.make .usd (← (ColCodec.fromCol (ColCodec.toCol p.minor) : Except String Nat))) = .ok p
  rw [nat_roundtrip p.minor (Nat.lt_of_le_of_lt p.le maxUnitPrice_lt)]
  simp only [bind, Except.bind]
  exact UnitPrice.make_minor p

/-! ## Entities -/

structure TenantRow where
  apiKey : ApiKey
  unitPrice : UnitPrice .usd
  deriving Repr, LeanDb.Entity

structure UsageEventRow where
  tenant : Ref TenantRow
  eventId : EventId
  quantity : Quantity
  occurredAt : Instant
  year : Nat
  month : Nat
  deriving Repr, LeanDb.Entity

structure LineRow where
  eventId : EventId
  quantity : Quantity
  unitPrice : Money .usd
  amount : Money .usd
  deriving Repr, LeanDb.Inline

structure InvoiceRow where
  tenant : Ref TenantRow
  year : Nat
  month : Nat
  total : Money .usd
  status : RowStatus
  lines : List LineRow
  deriving Repr

/-! ## Row ↔ domain -/

def tid (r : Ref TenantRow) : TenantId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩

def tref (t : TenantId) : Ref TenantRow := ⟨Int64.ofNat t.n⟩

def iid (r : LeanDb.Id InvoiceRow) : InvoiceId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩

def iref (i : InvoiceId) : LeanDb.Id InvoiceRow := ⟨Int64.ofNat i.n⟩

theorem tid_tref (t : TenantId) : tid (tref t) = t := by
  cases t with
  | mk n h => simp [tid, tref, Int64.toNatClampNeg_ofNat_of_lt h]

theorem iid_iref (i : InvoiceId) : iid (iref i) = i := by
  cases i with
  | mk n h => simp [iid, iref, Int64.toNatClampNeg_ofNat_of_lt h]

def TenantRow.toTenant (id : LeanDb.Id TenantRow) (r : TenantRow) : Tenant :=
  { id := tid ⟨id.toInt64⟩, unitPrice := r.unitPrice }

def LineRow.toLine (l : LineRow) : Line :=
  { eventId := l.eventId, quantity := l.quantity, unitPrice := l.unitPrice, amount := l.amount }

def LineRow.ofLine (l : Line) : LineRow :=
  { eventId := l.eventId, quantity := l.quantity, unitPrice := l.unitPrice, amount := l.amount }

theorem LineRow.toLine_ofLine (l : Line) : LineRow.toLine (LineRow.ofLine l) = l := rfl

def InvoiceRow.toInvoice (r : InvoiceRow) : Option Invoice :=
  match Period.make r.year r.month with
  | .error _ => none
  | .ok period => some
      { tenant := tid r.tenant
        period
        lines := r.lines.map LineRow.toLine
        total := r.total
        status := r.status.toDomain }

def InvoiceRow.ofInvoice (inv : Invoice) : InvoiceRow :=
  { tenant := tref inv.tenant
    year := inv.period.year
    month := inv.period.month
    total := inv.total
    status := RowStatus.ofStatus inv.status
    lines := inv.lines.map LineRow.ofLine }

def UsageEventRow.toEvent (r : UsageEventRow) : Option UsageEvent :=
  match Period.make r.year r.month with
  | .error _ => none
  | .ok period => some
      { tenant := tid r.tenant
        eventId := r.eventId
        quantity := r.quantity
        occurredAt := r.occurredAt
        period }

def UsageEventRow.ofEvent (e : UsageEvent) : UsageEventRow :=
  { tenant := tref e.tenant
    eventId := e.eventId
    quantity := e.quantity
    occurredAt := e.occurredAt
    year := e.period.year
    month := e.period.month }

/-! ## Invoice invariant = domain `Balanced` -/

@[leandb_invariant]
def InvoiceRow.invariant (r : InvoiceRow) : Bool :=
  match InvoiceRow.toInvoice r with
  | none => false
  | some inv => Balanced.holdsB inv

deriving instance LeanDb.Entity for InvoiceRow

instance : LeanDb.Indexes UsageEventRow := ⟨#[{ columns := #["tenant"] }]⟩
instance : LeanDb.Indexes InvoiceRow := ⟨#[{ columns := #["tenant"] }]⟩

unique% TenantRow.byApiKey := apiKey
unique% UsageEventRow.byTenantEvent := (tenant, eventId)
unique% InvoiceRow.byTenantPeriod := (tenant, year, month)

schema% BillingDb := TenantRow, UsageEventRow, InvoiceRow

def schema : List TableSpec := IsSchema.specs BillingDb

/-! ## Mapping laws -/

private theorem lines_roundtrip (ls : List Line) :
    (ls.map LineRow.ofLine).map LineRow.toLine = ls := by
  induction ls with
  | nil => rfl
  | cons _ _ ih => simp [LineRow.toLine, LineRow.ofLine, ih]

theorem InvoiceRow.toInvoice_ofInvoice (inv : Invoice) :
    InvoiceRow.toInvoice (InvoiceRow.ofInvoice inv) = some
      { inv with tenant := tid (tref inv.tenant) } := by
  unfold InvoiceRow.toInvoice InvoiceRow.ofInvoice
  rw [Period.make_ok, lines_roundtrip, RowStatus.toDomain_ofStatus]

theorem InvoiceRow.toInvoice_ofInvoice_id (inv : Invoice) :
    InvoiceRow.toInvoice (InvoiceRow.ofInvoice inv) = some inv := by
  have h := InvoiceRow.toInvoice_ofInvoice inv
  simp [tid_tref] at h
  exact h

theorem InvoiceRow.invariant_ofInvoice (inv : Invoice) (h : Balanced inv) :
    InvoiceRow.invariant (InvoiceRow.ofInvoice inv) = true := by
  simp [InvoiceRow.invariant, InvoiceRow.toInvoice_ofInvoice_id]
  exact (Balanced.holdsB_iff inv).mpr h

theorem InvoiceRow.Invariant_ofInvoice (inv : Invoice) (h : Balanced inv) :
    LeanDb.Invariant InvoiceRow (InvoiceRow.ofInvoice inv) := by
  show InvoiceRow.invariant (InvoiceRow.ofInvoice inv) = true
  exact InvoiceRow.invariant_ofInvoice inv h

/-- A checked invoice row from a balanced domain invoice. No runtime check. -/
def InvoiceRow.checked (inv : Invoice) (h : Balanced inv) : Checked InvoiceRow :=
  Checked.of (InvoiceRow.ofInvoice inv) (InvoiceRow.Invariant_ofInvoice inv h)

def InvoiceRow.checkedDraft {tenant : TenantId} {period : Period} {price : UnitPrice .usd}
    {events : List UsageEvent} {inv : DraftInvoice}
    (h : mkDraft tenant period price events = .ok inv) : Checked InvoiceRow :=
  InvoiceRow.checked inv.val (mkDraft_balanced h)

def InvoiceRow.checkedFinalize (inv : DraftInvoice) (h : Balanced inv.val) : Checked InvoiceRow :=
  InvoiceRow.checked (finalize inv).val (finalize_preserves_balanced inv h)

def InvoiceRow.checkedPay (inv : FinalizedInvoice) (h : Balanced inv.val) : Checked InvoiceRow :=
  InvoiceRow.checked (pay inv).val (pay_preserves_balanced inv h)

def InvoiceRow.checkedVoid (inv : FinalizedInvoice) (h : Balanced inv.val) : Checked InvoiceRow :=
  InvoiceRow.checked (voidInvoice inv).val (void_preserves_balanced inv h)

/-- Usage events have no extra invariant; every well-typed row is `Checked`. -/
def UsageEventRow.checked (e : UsageEvent) : Checked UsageEventRow :=
  Checked.of (UsageEventRow.ofEvent e) (by unfold LeanDb.Invariant; trivial)

def TenantRow.checked (r : TenantRow) : Checked TenantRow :=
  Checked.of r (by unfold LeanDb.Invariant; trivial)

def invoiceOf (s : Stored InvoiceRow) : Option (InvoiceId × Invoice) :=
  (InvoiceRow.toInvoice s.val).map fun inv => (iid s.id, inv)

def eventOf (s : Stored UsageEventRow) : Option UsageEvent :=
  UsageEventRow.toEvent s.val

end Billing.Schema
