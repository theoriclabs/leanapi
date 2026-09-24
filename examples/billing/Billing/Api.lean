/-
  Usage-based billing over LeanDB programs.

  Each endpoint's type says who may call it, what it reads or writes, and
  how it can fail. Duplicate usage events and duplicate invoices for a
  period are typed insert failures that become replays, not errors.
  Finalized invoices are updated only by `pay` and `void`, which keep
  the lines (domain theorems `pay_keeps_lines`, `void_keeps_lines`).
-/
import LeanApi.Http.DbEndpoint
import Billing.Policies
import Billing.Bypass

namespace Billing.Api

open LeanApi Lean LeanDb Billing Billing.Schema Billing.Policies PolicyView

/-! ## JSON and constructors -/

instance : SmartCtor EventId String := ⟨EventId.make, (·.raw)⟩
instance : SmartCtor Quantity Nat := ⟨Quantity.make, (·.n)⟩
instance : SmartCtor Instant Nat := ⟨Instant.make, (·.unixSec)⟩
instance : SmartCtor InvoiceId Nat := ⟨InvoiceId.make, (·.n)⟩
instance : SmartCtor ApiKey String := ⟨ApiKey.make, (·.raw)⟩

instance : FromBody Period where
  fromBody loc j := do
    let year ← field (α := Nat) loc j "year"
    let month ← field (α := Nat) loc j "month"
    match Period.make year month with
    | .ok p => .ok p
    | .error m => .error [⟨loc, m⟩]

structure UsageBody where
  eventId : EventId
  quantity : Quantity
  occurredAt : Instant
  period : Period

instance : FromBody UsageBody := .record
  (UsageBody.mk <$> .req "eventId" <*> .req "quantity" <*> .req "occurredAt" <*> .req "period")

structure InvoiceBody where
  period : Period

instance : FromBody InvoiceBody := .record (InvoiceBody.mk <$> .req "period")

def periodJson (p : Period) : Json :=
  Json.mkObj [("year", Json.num p.year), ("month", Json.num p.month)]

instance : ToJson LineView := ⟨fun l =>
  Json.mkObj [("eventId", .str l.eventId.raw), ("quantity", Json.num l.quantity.n),
    ("unitPrice", Json.num l.unitPriceMinor), ("amount", Json.num l.amountMinor)]⟩

instance : ToJson UsageView := ⟨fun v =>
  Json.mkObj [("eventId", .str v.eventId.raw), ("quantity", Json.num v.quantity.n),
    ("occurredAt", Json.num v.occurredAt.unixSec), ("period", periodJson v.period)]⟩

instance : ToJson InvoiceView := ⟨fun v =>
  Json.mkObj [("id", Json.num v.id.n), ("period", periodJson v.period),
    ("lines", Json.arr (v.lines.map toJson).toArray),
    ("total", Json.mkObj [("amount", Json.num v.totalMinor), ("currency", .str "usd")]),
    ("status", .str (toString v.status))]⟩

inductive Replayed (α : Type) where
  | fresh (a : α)
  | replay (a : α)

instance [ToResponse α] : ToResponse (Replayed α) where
  toRes
    | .fresh a => ToResponse.toRes a
    | .replay a => (ToResponse.toRes a).setHeader "idempotent-replayed" "true"

/-! ## Failures -/

inductive BillingError where
  | hidden
  | notDraft
  | notFinalized
  | tooManyLines
  | totalOutOfRange

instance : ToProblem BillingError where
  status
    | .hidden => ⟨404, by decide⟩
    | .notDraft | .notFinalized => ⟨409, by decide⟩
    | .tooManyLines | .totalOutOfRange => ⟨422, by decide⟩
  detail
    | .hidden => none
    | .notDraft => some "invoice is not a draft"
    | .notFinalized => some "invoice is not finalized"
    | .tooManyLines => some "too many lines"
    | .totalOutOfRange => some "invoice total is out of range"

def mkDraftError : String → BillingError
  | "too many lines" => .tooManyLines
  | _ => .totalOutOfRange

/-! ## Auth: a bearer token is the tenant's API key -/

def lookupTenant (t : String) : Read BillingDb (Option Tenant) :=
  match ApiKey.make t with
  | .error _ => pure none
  | .ok k =>
    (·.map fun row => TenantRow.toTenant row.id row.val) <$>
      Read.lookup TenantRow TenantRow.Unique.byApiKey k

instance billingAuth : AuthenticatesDb BillingDb Tenant :=
  AuthenticatesDb.sessions lookupTenant (realm := "billing")

/-! ## Ownership evidence for rows we construct as this tenant -/

theorem owns_event (p : Tenant) (e : UsageEvent) (h : e.tenant = p.id) :
    Owns.owns (s := BillingDb) p (UsageEventRow.ofEvent e) = true := by
  simp [Owns.owns, UsageEventRow.ofEvent, h, BEq.beq]

theorem owns_invoice (p : Tenant) (inv : Invoice) (h : inv.tenant = p.id) :
    Owns.owns (s := BillingDb) p (InvoiceRow.ofInvoice inv) = true := by
  simp [Owns.owns, InvoiceRow.ofInvoice, h, BEq.beq]

def usageViewOf (s : Stored UsageEventRow) : Option UsageView :=
  eventOf s |>.map projectUsage

def invoiceViewOf (s : Stored InvoiceRow) : Option InvoiceView :=
  invoiceOf s |>.map fun (id, inv) => projectInvoice id inv

/-- A visible invoice together with the domain proof that it is balanced. -/
def loadInvoice {σ} (p : Tenant) (id : InvoiceId) :
    TxnAs σ BillingDb p BillingError (Seen σ p InvoiceRow × { inv : Invoice // Balanced inv }) := do
  match ← TxnAs.get InvoiceRow (iref id) with
  | none => TxnAs.throw .hidden
  | some row =>
    match InvoiceRow.toInvoice row.val with
    | none => TxnAs.throw .hidden
    | some inv =>
      if hb : Balanced.holdsB inv then
        pure (row, ⟨inv, (Balanced.holdsB_iff inv).mp hb⟩)
      else TxnAs.throw .hidden

def viewOrHidden {σ} (p : Tenant) (s : Stored InvoiceRow) :
    TxnAs σ BillingDb p BillingError InvoiceView :=
  match invoiceViewOf s with
  | some v => pure v
  | none => TxnAs.throw .hidden

/-! ## Endpoints -/

/-- Report a usage event. Resending the same tenant and event id answers
    as the first time did: the unique-index clash is a replay. -/
def ingestUsage (me : Auth Tenant) (body : Body UsageBody) :
    Tx BillingDb BillingError (Replayed (Created UsageView)) :=
  WriteAs.toTx fun {_σ} => do
    let e : UsageEvent :=
      { tenant := me.val.id, eventId := body.val.eventId, quantity := body.val.quantity,
        occurredAt := body.val.occurredAt, period := body.val.period }
    let loc := s!"/usage/{e.eventId.raw}"
    let view := projectUsage e
    match ← TxnAs.insert (α := UsageEventRow) (UsageEventRow.checked e) (owns_event me.val e rfl) with
    | .ok _ =>
      pure (.fresh { val := view, location := some loc })
    | .error (.duplicate _ holder) =>
      match ← TxnAs.get UsageEventRow holder with
      | some row =>
        match usageViewOf row.toStored with
        | some v => pure (.replay { val := v, location := some loc })
        | none => TxnAs.throw .hidden
      | none => TxnAs.throw .hidden
    | .error (.missingRef _) => TxnAs.throw .hidden

/-- One of my usage events. Another tenant's event is a 404. -/
def readUsage (me : Auth Tenant) (id : Path EventId) :
    Read BillingDb (Except BillingError UsageView) := do
  match ← Scoped.where UsageEventRow me.val (fun r => r.val.eventId == id.val) with
  | [s] =>
    match usageViewOf s with
    | some v => return .ok v
    | none => return .error .hidden
  | _ => return .error .hidden

/-- Open a draft invoice for a period, rating my events in that month.
    A second open of the same period replays the first invoice. -/
def createInvoice (me : Auth Tenant) (body : Body InvoiceBody) :
    Tx BillingDb BillingError (Replayed (Created InvoiceView)) :=
  WriteAs.toTx fun {_σ} => do
    let rows ← TxnAs.all UsageEventRow
    let events := rows.filterMap eventOf
    match h : mkDraft me.val.id body.val.period me.val.unitPrice events with
    | .error msg => TxnAs.throw (mkDraftError msg)
    | .ok inv =>
      have htenant : inv.val.tenant = me.val.id := (mkDraft_ok h).1
      match ← TxnAs.insert (α := InvoiceRow) (InvoiceRow.checkedDraft h) (owns_invoice me.val inv.val htenant) with
      | .ok row =>
        match invoiceViewOf row.toStored with
        | some v =>
          pure (.fresh { val := v, location := some s!"/invoices/{v.id.n}" })
        | none => TxnAs.throw .hidden
      | .error (.duplicate _ holder) =>
        match ← TxnAs.get InvoiceRow holder with
        | some row =>
          match invoiceViewOf row.toStored with
          | some v =>
            pure (.replay { val := v, location := some s!"/invoices/{v.id.n}" })
          | none => TxnAs.throw .hidden
        | none => TxnAs.throw .hidden
      | .error (.missingRef _) => TxnAs.throw .hidden

/-- One of my invoices. Another tenant's invoice is a 404. -/
def readInvoice (me : Auth Tenant) (id : Path InvoiceId) :
    Read BillingDb (Except BillingError InvoiceView) :=
  ReadAs.forAuth me fun _a => do
    match ← ReadAs.get InvoiceRow (iref id.val) with
    | some s =>
      match invoiceViewOf s with
      | some v => return .ok v
      | none => return .error .hidden
    | none => return .error .hidden

private def updateOwned {σ} (p : Tenant) (row : Seen σ p InvoiceRow)
    (new : Invoice) (hb : Balanced new) :
    TxnAs σ BillingDb p BillingError InvoiceView :=
  if howns : Owns.owns (s := BillingDb) p (InvoiceRow.ofInvoice new) = true then do
    match ← TxnAs.update (α := InvoiceRow) row (InvoiceRow.checked new hb) howns with
    | .ok stored => viewOrHidden p stored
    | .error (.stale _) | .error .gone | .error (.missingRef _) => TxnAs.throw .hidden
    | .error (.duplicate _ _) => TxnAs.throw .hidden
  else TxnAs.throw .hidden

/-- Finalize a draft. Lines and total stay; status becomes finalized. -/
def finalizeInvoice (me : Auth Tenant) (id : Path InvoiceId) :
    Tx BillingDb BillingError InvoiceView :=
  WriteAs.toTx fun {_σ} => do
    let (row, packed) ← loadInvoice me.val id.val
    if hst : packed.val.status = .draft then
      let d : DraftInvoice := ⟨packed.val, hst⟩
      updateOwned me.val row (finalize d).val (finalize_preserves_balanced d packed.property)
    else TxnAs.throw .notDraft

/-- Mark a finalized invoice paid. Lines do not change. -/
def payInvoice (me : Auth Tenant) (id : Path InvoiceId) :
    Tx BillingDb BillingError InvoiceView :=
  WriteAs.toTx fun {_σ} => do
    let (row, packed) ← loadInvoice me.val id.val
    if hst : packed.val.status = .sealed .finalized then
      let f : FinalizedInvoice := ⟨packed.val, hst⟩
      updateOwned me.val row (pay f).val (pay_preserves_balanced f packed.property)
    else TxnAs.throw .notFinalized

/-- Void a finalized invoice. Lines do not change. -/
def voidInvoiceEp (me : Auth Tenant) (id : Path InvoiceId) :
    Tx BillingDb BillingError InvoiceView :=
  WriteAs.toTx fun {_σ} => do
    let (row, packed) ← loadInvoice me.val id.val
    if hst : packed.val.status = .sealed .finalized then
      let f : FinalizedInvoice := ⟨packed.val, hst⟩
      updateOwned me.val row (voidInvoice f).val (void_preserves_balanced f packed.property)
    else TxnAs.throw .notFinalized

/-! ## The HTTP surface -/

def billingApi : DbApi BillingDb := api! [
  .post "/usage"                       ingestUsage,
  .get  "/usage/{eventId}"             readUsage,
  .post "/invoices"                    createInvoice,
  .get  "/invoices/{id:nat}"           readInvoice,
  .post "/invoices/{id:nat}/finalize"  finalizeInvoice,
  .post "/invoices/{id:nat}/pay"       payInvoice,
  .post "/invoices/{id:nat}/void"      voidInvoiceEp
]

def stack (log : String → IO Unit := IO.eprintln) (ready : IO Bool := pure true) : Stack :=
  Stack.of [recover log, requestId, accessLog log, health ready, securityHeaders, timeout 10000]

def service (dc : DbConns) (log : String → IO Unit := IO.eprintln) : Service :=
  billingApi.service dc (stack log) log

/-- error: could not synthesize default value for parameter 'safe' using tactics
---
error: a GET or HEAD endpoint must not change state, but this handler's effect is `writes`. Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.
⊢ (Handler.effect (DbState BillingDb)
      (Auth Tenant → Body UsageBody → LeanApi.Tx BillingDb BillingError (Replayed (Created UsageView)))).Safe -/
#guard_msgs (error) in
example : DbEndpoint BillingDb := .get "/usage" ingestUsage

end Billing.Api
