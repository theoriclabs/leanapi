/-
  Usage-based billing, as pure types and functions. No HTTP, no SQL.

  A tenant reports usage events. Each event is counted once. An invoice
  for a period is the rated snapshot of those events: its total is the
  sum of its lines. Once finalized, the lines never change; the only
  moves left are to paid or void.

  Theorems here are about these functions. They are not about the
  database: at the pinned LeanDB, `DbState` is empty in proofs.
-/
import LeanApi.Props.Stored

namespace Billing

open LeanApi.Props

/-! ## Bounds

Every stored `Nat` must sit below 2^63 (LeanDB D7). Quantity, unit
price and line count are bounded so a total cannot overflow that. -/

def maxQty : Nat := 1_000_000
def maxUnitPrice : Nat := 100_000_000
def maxLines : Nat := 10_000
def maxTotal : Nat := maxLines * maxQty * maxUnitPrice

theorem maxQty_lt : maxQty < 2 ^ 63 := by decide
theorem maxUnitPrice_lt : maxUnitPrice < 2 ^ 63 := by decide
theorem maxLines_lt : maxLines < 2 ^ 63 := by decide
theorem maxTotal_lt : maxTotal < 2 ^ 63 := by decide
theorem maxLines_pos : 0 < maxLines := by decide

theorem mul_le_maxTotal (q p : Nat) (hq : q ≤ maxQty) (hp : p ≤ maxUnitPrice) :
    q * p ≤ maxTotal := by
  have hprod : q * p ≤ maxQty * maxUnitPrice := Nat.mul_le_mul hq hp
  have hscale : maxQty * maxUnitPrice ≤ maxLines * (maxQty * maxUnitPrice) :=
    Nat.le_mul_of_pos_left (maxQty * maxUnitPrice) maxLines_pos
  exact Nat.le_trans hprod (by simpa [maxTotal, Nat.mul_assoc] using hscale)

/-! ## Identifiers and units -/

/-- One currency. Arithmetic of different currencies does not type-check. -/
inductive Currency where
  | usd
  deriving DecidableEq, Repr

instance : ToString Currency := ⟨fun | .usd => "usd"⟩

/-- A tenant id. It fits in a LeanDB `Ref` (below 2^63). -/
structure TenantId where
  n : Nat
  lt : n < 2 ^ 63 := by decide
  deriving DecidableEq, Repr

instance : ToString TenantId := ⟨fun t => toString t.n⟩

def TenantId.make (n : Nat) : Except String TenantId :=
  if h : n == 0 || n >= 2 ^ 63 then .error "tenant id must be between 1 and 2^63-1"
  else .ok ⟨n, by simp at h; omega⟩

def TenantId.ofNat! (n : Nat) : TenantId :=
  if h : n < 2 ^ 63 then ⟨n, h⟩ else ⟨0, by decide⟩

structure InvoiceId where
  n : Nat
  lt : n < 2 ^ 63 := by decide
  deriving DecidableEq, Repr

instance : ToString InvoiceId := ⟨fun i => toString i.n⟩

def InvoiceId.make (n : Nat) : Except String InvoiceId :=
  if h : n == 0 || n >= 2 ^ 63 then .error "invoice id must be between 1 and 2^63-1"
  else .ok ⟨n, by simp at h; omega⟩

def eventIdValid (s : String) : Bool :=
  !s.isEmpty && s.length ≤ 64 &&
    s.all (fun c => c.toNat > 32 && c.toNat < 127 && c != '/')

/-- An event id chosen by the sender, for deduplication. -/
structure EventId where
  raw : String
  ok : eventIdValid raw = true
  deriving DecidableEq, Repr

def EventId.valid := eventIdValid

def EventId.make (s : String) : Except String EventId :=
  if h : eventIdValid s then .ok ⟨s, h⟩
  else .error "event id must be 1–64 visible ASCII characters, no '/'"

theorem EventId.make_raw (e : EventId) : EventId.make e.raw = .ok e := by
  unfold EventId.make; simp [e.ok]

/-- UTC instant: seconds since the Unix epoch. -/
structure Instant where
  unixSec : Nat
  lt : unixSec < 2 ^ 63 := by decide
  deriving DecidableEq, Repr

def Instant.make (n : Nat) : Except String Instant :=
  if h : n < 2 ^ 63 then .ok ⟨n, h⟩ else .error "timestamp is out of range"

theorem Instant.make_unixSec (t : Instant) : Instant.make t.unixSec = .ok t := by
  unfold Instant.make; simp [t.lt]

/-- A calendar month the event is billed in. -/
structure Period where
  year : Nat
  month : Nat
  yearOk : 1970 ≤ year ∧ year ≤ 2100
  monthOk : 1 ≤ month ∧ month ≤ 12
  deriving DecidableEq, Repr

def Period.make (year month : Nat) : Except String Period :=
  if hy : 1970 ≤ year ∧ year ≤ 2100 then
    if hm : 1 ≤ month ∧ month ≤ 12 then .ok ⟨year, month, hy, hm⟩
    else .error "month must be between 1 and 12"
  else .error "year must be between 1970 and 2100"

theorem Period.make_ok (p : Period) : Period.make p.year p.month = .ok p := by
  unfold Period.make
  simp [p.yearOk, p.monthOk]

/-- Units consumed: at least one, at most `maxQty`. -/
structure Quantity where
  n : Nat
  pos : 1 ≤ n
  le : n ≤ maxQty
  deriving DecidableEq, Repr

def Quantity.make (n : Nat) : Except String Quantity :=
  if h : 1 ≤ n ∧ n ≤ maxQty then .ok ⟨n, h.1, h.2⟩
  else .error "quantity must be between 1 and 1000000"

theorem Quantity.make_n (q : Quantity) : Quantity.make q.n = .ok q := by
  unfold Quantity.make; simp [q.pos, q.le]

theorem Quantity.lt (q : Quantity) : q.n < 2 ^ 63 :=
  Nat.lt_of_le_of_lt q.le maxQty_lt

/-- Money in minor units (cents), tagged with a currency. -/
structure Money (c : Currency) where
  minor : Nat
  le : minor ≤ maxTotal
  deriving DecidableEq, Repr

def Money.make (c : Currency) (n : Nat) : Except String (Money c) :=
  if h : n ≤ maxTotal then .ok ⟨n, h⟩ else .error "amount is out of range"

theorem Money.lt {c : Currency} (m : Money c) : m.minor < 2 ^ 63 :=
  Nat.lt_of_le_of_lt m.le maxTotal_lt

/-- A unit price is money that cannot exceed `maxUnitPrice`. -/
structure UnitPrice (c : Currency) where
  minor : Nat
  le : minor ≤ maxUnitPrice
  deriving DecidableEq, Repr

def UnitPrice.make (c : Currency) (n : Nat) : Except String (UnitPrice c) :=
  if h : n ≤ maxUnitPrice then .ok ⟨n, h⟩ else .error "unit price is out of range"

def UnitPrice.toMoney {c : Currency} (p : UnitPrice c) : Money c :=
  ⟨p.minor, Nat.le_trans p.le (Nat.le_trans
    (Nat.le_mul_of_pos_left maxUnitPrice (by decide : 0 < maxQty))
    (by
      have : maxQty * maxUnitPrice ≤ maxTotal := by
        simpa [maxTotal, Nat.mul_assoc] using
          Nat.le_mul_of_pos_left (maxQty * maxUnitPrice) maxLines_pos
      exact this))⟩

def apiKeyValid (s : String) : Bool :=
  8 ≤ s.length ∧ s.length ≤ 64 &&
    s.all (fun c => c.toNat > 32 && c.toNat < 127 && c != '/')

/-- An API key that identifies a tenant. -/
structure ApiKey where
  raw : String
  ok : apiKeyValid raw = true
  deriving DecidableEq, Repr

def ApiKey.valid := apiKeyValid

def ApiKey.make (s : String) : Except String ApiKey :=
  if h : apiKeyValid s then .ok ⟨s, h⟩
  else .error "API key must be 8–64 visible ASCII characters, no '/'"

/-! ## Domain records -/

structure Tenant where
  id : TenantId
  unitPrice : UnitPrice .usd
  deriving DecidableEq, Repr

structure UsageEvent where
  tenant : TenantId
  eventId : EventId
  quantity : Quantity
  occurredAt : Instant
  period : Period
  deriving DecidableEq, Repr

/-- One rated line of an invoice. `amount` is `quantity × unitPrice`. -/
structure Line where
  eventId : EventId
  quantity : Quantity
  unitPrice : Money .usd
  amount : Money .usd
  deriving DecidableEq, Repr

/-- A sealed invoice is finalized, paid, or void. -/
inductive Seal where
  | finalized
  | paid
  | void
  deriving DecidableEq, Repr

/-- Invoice lifecycle. The type of `finalize` / `pay` / `voidInvoice`
    is the specification of which moves exist. -/
inductive Status where
  | draft
  | sealed (s : Seal)
  deriving DecidableEq, Repr

instance : ToString Status := ⟨fun
  | .draft => "draft"
  | .sealed .finalized => "finalized"
  | .sealed .paid => "paid"
  | .sealed .void => "void"⟩

structure Invoice where
  tenant : TenantId
  period : Period
  lines : List Line
  total : Money .usd
  status : Status
  deriving DecidableEq, Repr

abbrev DraftInvoice := { inv : Invoice // inv.status = .draft }
abbrev FinalizedInvoice := { inv : Invoice // inv.status = .sealed .finalized }
abbrev PaidInvoice := { inv : Invoice // inv.status = .sealed .paid }
abbrev VoidInvoice := { inv : Invoice // inv.status = .sealed .void }

/-! ## Rating and ingest (pure) -/

/-- Two events collide when they share a tenant and an event id. -/
def sameEvent (a b : UsageEvent) : Bool :=
  a.tenant == b.tenant && a.eventId == b.eventId

def hasEvent (log : List UsageEvent) (e : UsageEvent) : Bool :=
  log.any (sameEvent e)

/-- Add `e` to the log, or do nothing if it is already there. -/
def ingest (log : List UsageEvent) (e : UsageEvent) : List UsageEvent :=
  if hasEvent log e then log else log ++ [e]

def Line.rate (price : UnitPrice .usd) (e : UsageEvent) : Line :=
  { eventId := e.eventId
    quantity := e.quantity
    unitPrice := price.toMoney
    amount := ⟨e.quantity.n * price.minor, mul_le_maxTotal e.quantity.n price.minor e.quantity.le price.le⟩ }

def sumAmounts : List Line → Nat
  | [] => 0
  | l :: ls => l.amount.minor + sumAmounts ls

def rateLog (price : UnitPrice .usd) (log : List UsageEvent) : Nat :=
  sumAmounts (log.map (Line.rate price))

def eventsInPeriod (period : Period) (log : List UsageEvent) : List UsageEvent :=
  log.filter (fun e => e.period == period)

/-! ## Invoice construction and transitions -/

def Line.priced (l : Line) : Prop :=
  l.amount.minor = l.quantity.n * l.unitPrice.minor

def Invoice.balanced (inv : Invoice) : Prop :=
  inv.total.minor = sumAmounts inv.lines

/-- A stored invoice: total equals the lines, each line is priced, not
    too many lines. Declared once; storage runs the generated check. -/
invariant Balanced (inv : Invoice) where
  total_eq : inv.total.minor = sumAmounts inv.lines
  priced : inv.lines.all (fun l => l.amount.minor == l.quantity.n * l.unitPrice.minor) = true
  bounded : inv.lines.length ≤ maxLines

def mkDraft (tenant : TenantId) (period : Period) (price : UnitPrice .usd)
    (events : List UsageEvent) : Except String DraftInvoice :=
  let uniq := events.foldl ingest []
  let billed := eventsInPeriod period uniq
  let lines := billed.map (Line.rate price)
  if _hlen : lines.length ≤ maxLines then
    let totalN := sumAmounts lines
    if htot : totalN ≤ maxTotal then
      .ok ⟨{ tenant, period, lines, total := ⟨totalN, htot⟩, status := .draft }, rfl⟩
    else .error "invoice total is out of range"
  else .error "too many lines"

def finalize (inv : DraftInvoice) : FinalizedInvoice :=
  ⟨{ inv.val with status := .sealed .finalized }, rfl⟩

def pay (inv : FinalizedInvoice) : PaidInvoice :=
  ⟨{ inv.val with status := .sealed .paid }, rfl⟩

def voidInvoice (inv : FinalizedInvoice) : VoidInvoice :=
  ⟨{ inv.val with status := .sealed .void }, rfl⟩

/-- Lines of a draft may change; a sealed invoice has no such function. -/
def replaceLines (inv : DraftInvoice) (lines : List Line) (htot : sumAmounts lines ≤ maxTotal)
    (_hlen : lines.length ≤ maxLines) : DraftInvoice :=
  ⟨{ inv.val with lines, total := ⟨sumAmounts lines, htot⟩, status := .draft }, rfl⟩

/-! ## Ingest: counted exactly once -/

theorem sameEvent_self (e : UsageEvent) : sameEvent e e = true := by
  simp [sameEvent]

theorem hasEvent_snoc (log : List UsageEvent) (e : UsageEvent) :
    hasEvent (log ++ [e]) e = true := by
  simp [hasEvent, List.any_append, sameEvent_self]

/-- Ingesting the same event twice equals ingesting it once. -/
theorem ingest_idem (log : List UsageEvent) (e : UsageEvent) :
    ingest (ingest log e) e = ingest log e := by
  unfold ingest
  cases h : hasEvent log e
  · have : hasEvent (log ++ [e]) e = true := hasEvent_snoc log e
    simp [this]
  · simp [h]

/-- Folding `ingest` over a list that already contains `e` leaves it. -/
theorem ingest_already (log : List UsageEvent) (e : UsageEvent)
    (h : hasEvent log e = true) : ingest log e = log := by
  simp [ingest, h]

theorem ingest_new (log : List UsageEvent) (e : UsageEvent)
    (h : hasEvent log e = false) : ingest log e = log ++ [e] := by
  simp [ingest, h]

/-! ## Rating adds over concatenation -/

theorem sumAmounts_nil : sumAmounts [] = 0 := rfl

theorem sumAmounts_cons (l : Line) (ls : List Line) :
    sumAmounts (l :: ls) = l.amount.minor + sumAmounts ls := rfl

theorem sumAmounts_append (xs ys : List Line) :
    sumAmounts (xs ++ ys) = sumAmounts xs + sumAmounts ys := by
  induction xs with
  | nil => simp [sumAmounts]
  | cons l ls ih =>
    simp [sumAmounts, ih, Nat.add_assoc]

/-- Rating a concatenation is the sum of the ratings. Disjointness is
    the business meaning: `ingest` never puts the same event in twice,
    so the lists we rate do not overlap. -/
theorem rateLog_append (price : UnitPrice .usd) (xs ys : List UsageEvent) :
    rateLog price (xs ++ ys) = rateLog price xs + rateLog price ys := by
  simp [rateLog, List.map_append, sumAmounts_append]

/-- Rating is unchanged by ingesting an event that is already in the log. -/
theorem rateLog_ingest_idem (price : UnitPrice .usd) (log : List UsageEvent) (e : UsageEvent) :
    rateLog price (ingest (ingest log e) e) = rateLog price (ingest log e) := by
  rw [ingest_idem]

theorem Line.rate_priced (price : UnitPrice .usd) (e : UsageEvent) :
    (Line.rate price e).amount.minor =
      (Line.rate price e).quantity.n * (Line.rate price e).unitPrice.minor := by
  simp [Line.rate, UnitPrice.toMoney]

theorem lines_rated_priced (price : UnitPrice .usd) (es : List UsageEvent) :
    (es.map (Line.rate price)).all
      (fun l => l.amount.minor == l.quantity.n * l.unitPrice.minor) = true := by
  induction es with
  | nil => simp
  | cons e es ih =>
    simp [Line.rate_priced, ih]

/-! ## An invoice's total is the sum of its lines -/

theorem mkDraft_ok {tenant : TenantId} {period : Period} {price : UnitPrice .usd}
    {events : List UsageEvent} {inv : DraftInvoice}
    (h : mkDraft tenant period price events = .ok inv) :
    inv.val.tenant = tenant ∧ inv.val.period = period ∧ inv.val.status = .draft ∧
      inv.val.total.minor = sumAmounts inv.val.lines ∧
      inv.val.lines.length ≤ maxLines := by
  unfold mkDraft at h
  simp only at h
  split at h
  · split at h
    · cases h
      exact ⟨rfl, rfl, rfl, rfl, ‹_›⟩
    · cases h
  · cases h

theorem mkDraft_balanced {tenant : TenantId} {period : Period} {price : UnitPrice .usd}
    {events : List UsageEvent} {inv : DraftInvoice}
    (h : mkDraft tenant period price events = .ok inv) :
    Balanced inv.val := by
  obtain ⟨_, _, _, ht, hb⟩ := mkDraft_ok h
  refine ⟨ht, ?_, hb⟩
  unfold mkDraft at h
  simp only at h
  split at h
  · split at h
    · cases h
      exact lines_rated_priced price _
    · cases h
  · cases h

/-! ## Transitions out of finalized keep the lines -/

theorem finalize_keeps_lines (inv : DraftInvoice) :
    (finalize inv).val.lines = inv.val.lines ∧
      (finalize inv).val.total = inv.val.total :=
  ⟨rfl, rfl⟩

theorem pay_keeps_lines (inv : FinalizedInvoice) :
    (pay inv).val.lines = inv.val.lines ∧ (pay inv).val.total = inv.val.total :=
  ⟨rfl, rfl⟩

theorem void_keeps_lines (inv : FinalizedInvoice) :
    (voidInvoice inv).val.lines = inv.val.lines ∧
      (voidInvoice inv).val.total = inv.val.total :=
  ⟨rfl, rfl⟩

theorem pay_status (inv : FinalizedInvoice) :
    (pay inv).val.status = .sealed .paid := rfl

theorem void_status (inv : FinalizedInvoice) :
    (voidInvoice inv).val.status = .sealed .void := rfl

theorem finalize_status (inv : DraftInvoice) :
    (finalize inv).val.status = .sealed .finalized := rfl

theorem pay_preserves_balanced (inv : FinalizedInvoice) (h : Balanced inv.val) :
    Balanced (pay inv).val := by
  obtain ⟨ht, hp, hb⟩ := h
  exact ⟨ht, hp, hb⟩

theorem void_preserves_balanced (inv : FinalizedInvoice) (h : Balanced inv.val) :
    Balanced (voidInvoice inv).val := by
  obtain ⟨ht, hp, hb⟩ := h
  exact ⟨ht, hp, hb⟩

theorem finalize_preserves_balanced (inv : DraftInvoice) (h : Balanced inv.val) :
    Balanced (finalize inv).val := by
  obtain ⟨ht, hp, hb⟩ := h
  exact ⟨ht, hp, hb⟩

/-- The only transitions out of `finalized` are to `paid` or `void`. -/
inductive Next : Status → Status → Prop
  | pay : Next (.sealed .finalized) (.sealed .paid)
  | void : Next (.sealed .finalized) (.sealed .void)

theorem pay_next (inv : FinalizedInvoice) :
    Next inv.val.status (pay inv).val.status := by
  rw [inv.property, pay_status]; exact .pay

theorem void_next (inv : FinalizedInvoice) :
    Next inv.val.status (voidInvoice inv).val.status := by
  rw [inv.property, void_status]; exact .void

/-! ## What the types refuse

`replaceLines` accepts a `DraftInvoice`. Applying it to a finalized
invoice is a type error: there is no such function. -/

/-- error: Application type mismatch: The argument
  inv
has type
  FinalizedInvoice
but is expected to have type
  DraftInvoice
in the application
  replaceLines inv -/
#guard_msgs (error, drop warning) in
example (inv : FinalizedInvoice) (ls : List Line) (htot : sumAmounts ls ≤ maxTotal)
    (hlen : ls.length ≤ maxLines) : DraftInvoice :=
  replaceLines inv ls htot hlen

/-- error: Application type mismatch: The argument
  inv
has type
  DraftInvoice
but is expected to have type
  FinalizedInvoice
in the application
  pay inv -/
#guard_msgs (error, drop warning) in
example (inv : DraftInvoice) : PaidInvoice := pay inv

end Billing
