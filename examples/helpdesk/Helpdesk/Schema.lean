/-
  LeanDB mapping for the help desk. Column codecs go through the same
  constructors as the HTTP extractors. Every policy-relevant field (org,
  requester, author role, internal) lives on the row itself.

  Avoided LeanDB limits (review D1–D10): no child-list filters, no order
  by closed enums, no `Option (Ref _)`, no cascades, no `append`, Nats
  bounded below 2^63, every policy single-table.
-/
import LeanDb
import Helpdesk.Domain

namespace Helpdesk

open LeanDb

/-! ## Closed enums and codecs -/

deriving instance LeanDb.ClosedEnum for Role
deriving instance LeanDb.ClosedEnum for TicketStatus

instance : ColCodec Subject := ColCodec.via (β := String) (·.raw) Subject.make
instance : ColCodec BodyText := ColCodec.via (β := String) (·.raw) BodyText.make
instance : ColCodec EmailMessageId := ColCodec.via (β := String) (·.raw) EmailMessageId.make
instance : ColCodec Instant := ColCodec.via (β := Nat) (·.unixSeconds) Instant.make

theorem nat_roundtrip (n : Nat) (h : n < 2^63) :
    (ColCodec.fromCol (ColCodec.toCol n) : Except String Nat) = .ok n := by
  have h1 : ¬ (Int64.ofNat n < 0) := by
    rw [Int64.lt_iff_toInt_lt]; simp [Int64.toInt_ofNat_of_lt h]
  have hmax : LeanDb.natSqlMax = 2^63 - 1 := by decide
  have hs : LeanDb.natToSql n = some (Int64.ofNat n) := by
    simp only [LeanDb.natToSql, hmax]; split <;> first | rfl | omega
  simp [ColCodec.fromCol, ColCodec.toCol, hs, h1, Int64.toNatClampNeg_ofNat_of_lt h]

theorem Instant.make_unix (t : Instant) : Instant.make t.unixSeconds = .ok t := by
  unfold Instant.make; simp [t.lt]

theorem instant_roundtrip (t : Instant) :
    (ColCodec.fromCol (ColCodec.toCol t) : Except String Instant) = .ok t := by
  show (do Instant.make (← (ColCodec.fromCol (ColCodec.toCol t.unixSeconds) : Except String Nat))) = .ok t
  rw [nat_roundtrip t.unixSeconds t.lt]
  simp [Bind.bind, Except.bind, Instant.make_unix]

/-! ## Entities -/

structure OrgRow where
  name : String
  deriving Repr, LeanDb.Entity

structure UserRow where
  org : Ref OrgRow
  name : String
  role : Role
  tokenDigest : String
  deriving Repr, LeanDb.Entity

structure TicketRow where
  org : Ref OrgRow
  requester : Ref UserRow
  subject : Subject
  status : TicketStatus
  inboundId : EmailMessageId
  openedAt : Instant
  deriving Repr, LeanDb.Entity

structure MessageRow where
  org : Ref OrgRow
  ticket : Ref TicketRow
  author : Ref UserRow
  requester : Ref UserRow
  authorRole : Role
  body : BodyText
  internal : Bool
  createdAt : Instant
  deriving Repr

/-- A customer is never recorded as the author of an internal note. -/
@[leandb_invariant]
def MessageRow.invariant (r : MessageRow) : Bool :=
  Bool.not (decide (r.authorRole = .customer) && r.internal)

deriving instance LeanDb.Entity for MessageRow

unique% OrgRow.byName := name
unique% UserRow.byToken := tokenDigest
unique% TicketRow.byInbound := (org, inboundId)

schema% HelpdeskDb := OrgRow, UserRow, TicketRow, MessageRow

def schema : List TableSpec := IsSchema.specs HelpdeskDb

/-! ## Id mapping -/

def oid (r : Ref OrgRow) : OrgId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩
def oref (o : OrgId) : Ref OrgRow := ⟨Int64.ofNat o.n⟩

def uid (r : Ref UserRow) : UserId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩
def uref (u : UserId) : Ref UserRow := ⟨Int64.ofNat u.n⟩

def tid (r : Ref TicketRow) : TicketId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩
def tref (t : TicketId) : Ref TicketRow := ⟨Int64.ofNat t.n⟩

def mid (r : Ref MessageRow) : MessageId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩

theorem oid_lt (r : Ref OrgRow) : (oid r).n < 2^63 := (oid r).lt
theorem uid_lt (r : Ref UserRow) : (uid r).n < 2^63 := (uid r).lt
theorem tid_lt (r : Ref TicketRow) : (tid r).n < 2^63 := (tid r).lt

theorem oid_oref (o : OrgId) : oid (oref o) = o := by
  cases o with | mk n h => simp [oid, oref, Int64.toNatClampNeg_ofNat_of_lt h]

theorem uid_uref (u : UserId) : uid (uref u) = u := by
  cases u with | mk n h => simp [uid, uref, Int64.toNatClampNeg_ofNat_of_lt h]

theorem tid_tref (t : TicketId) : tid (tref t) = t := by
  cases t with | mk n h => simp [tid, tref, Int64.toNatClampNeg_ofNat_of_lt h]

/-- A `Ref` that `==` `oref o` reconstructs to `o`. The converse can fail
    for a negative `Int64` (the mapping clamps); stored ids are
    non-negative. -/
theorem beq_oref_implies_oid (r : Ref OrgRow) (o : OrgId)
    (h : (r == oref o) = true) : oid r = o := by
  change (r.toInt64 == Int64.ofNat o.n) = true at h
  have h64 : r.toInt64 = Int64.ofNat o.n := (beq_iff_eq).mp h
  cases o with
  | mk n hn =>
    simp [oid, h64, Int64.toNatClampNeg_ofNat_of_lt hn]

theorem beq_uref_implies_uid (r : Ref UserRow) (u : UserId)
    (h : (r == uref u) = true) : uid r = u := by
  change (r.toInt64 == Int64.ofNat u.n) = true at h
  have h64 : r.toInt64 = Int64.ofNat u.n := (beq_iff_eq).mp h
  cases u with
  | mk n hn =>
    simp [uid, h64, Int64.toNatClampNeg_ofNat_of_lt hn]

theorem oref_inj {a b : OrgId} (h : (oref a == oref b) = true) : a = b := by
  have := beq_oref_implies_oid (oref a) b h
  simpa [oid_oref] using this

theorem uref_inj {a b : UserId} (h : (uref a == uref b) = true) : a = b := by
  have := beq_uref_implies_uid (uref a) b h
  simpa [uid_uref] using this

theorem oref_beq_self (o : OrgId) : (oref o == oref o) = true := by
  change (Int64.ofNat o.n == Int64.ofNat o.n) = true
  exact beq_self_eq_true _

theorem uref_beq_self (u : UserId) : (uref u == uref u) = true := by
  change (Int64.ofNat u.n == Int64.ofNat u.n) = true
  exact beq_self_eq_true _

theorem oref_beq_of_eq {a b : OrgId} (h : a = b) : (oref a == oref b) = true := by
  rw [h]; exact oref_beq_self b

theorem uref_beq_of_eq {a b : UserId} (h : a = b) : (uref a == uref b) = true := by
  rw [h]; exact uref_beq_self b

/-! ## Row ↔ domain -/

def TicketRow.toTicket (id : LeanDb.Id TicketRow) (r : TicketRow) : Ticket :=
  { id := tid id, org := oid r.org, requester := uid r.requester, subject := r.subject,
    status := r.status, inboundId := r.inboundId, openedAt := r.openedAt }

def TicketRow.ofTicket (t : Ticket) : TicketRow :=
  { org := oref t.org, requester := uref t.requester, subject := t.subject,
    status := t.status, inboundId := t.inboundId, openedAt := t.openedAt }

def MessageRow.toMessage (id : LeanDb.Id MessageRow) (r : MessageRow) : Message :=
  { id := mid id, org := oid r.org, ticket := tid r.ticket, author := uid r.author,
    requester := uid r.requester, authorRole := r.authorRole, body := r.body,
    internal := r.internal, createdAt := r.createdAt }

def MessageRow.ofMessage (m : Message) : MessageRow :=
  { org := oref m.org, ticket := tref m.ticket, author := uref m.author,
    requester := uref m.requester, authorRole := m.authorRole, body := m.body,
    internal := m.internal, createdAt := m.createdAt }

def reconstructTicket (s : Stored TicketRow) : Ticket := s.val.toTicket s.id
def reconstructMessage (s : Stored MessageRow) : Message := s.val.toMessage s.id

/-! ## The invariant is `Message.ok` -/

private theorem not_and_imp_bool (b internal : Bool) :
    (b && internal) = false ↔ (b = true → internal = false) := by
  cases b <;> cases internal <;> simp

private theorem bool_not_true (b : Bool) : (!b) = true ↔ b = false := by
  cases b <;> simp

theorem MessageRow.invariant_iff (r : MessageRow) (i : LeanDb.Id MessageRow) :
    MessageRow.invariant r = true ↔ Message.ok (r.toMessage i) := by
  have key := not_and_imp_bool (decide (r.authorRole = .customer)) r.internal
  constructor
  · intro hi hp
    have : r.authorRole = .customer := by
      simpa [MessageRow.toMessage] using hp
    have hfalse : (decide (r.authorRole = .customer) && r.internal) = false :=
      (bool_not_true _).mp hi
    exact key.mp hfalse (decide_eq_true_iff.mpr this)
  · intro hok
    refine (bool_not_true _).mpr (key.mpr ?_)
    intro hd
    have : r.authorRole = .customer := decide_eq_true_iff.mp hd
    have : (r.toMessage i).authorRole = .customer := by
      simpa [MessageRow.toMessage] using this
    exact hok this

theorem MessageRow.Invariant_iff (r : MessageRow) (i : LeanDb.Id MessageRow) :
    LeanDb.Invariant MessageRow r ↔ Message.ok (r.toMessage i) := by
  show MessageRow.invariant r = true ↔ _
  exact MessageRow.invariant_iff r i

theorem MessageRow.ofMessage_invariant (m : Message) (h : Message.ok m) :
    LeanDb.Invariant MessageRow (MessageRow.ofMessage m) := by
  rw [MessageRow.Invariant_iff _ ⟨0⟩]
  exact h

/-- A checked message row from a well-formed domain message. No runtime check. -/
def MessageRow.checked (m : Message) (h : Message.ok m) : Checked MessageRow :=
  Checked.of (MessageRow.ofMessage m) (MessageRow.ofMessage_invariant m h)

/-- An inbound ticket: always `open`, so `Checked` is free (no row invariant). -/
def TicketRow.checked (t : Ticket) : Checked TicketRow :=
  Checked.of (TicketRow.ofTicket t) trivial

def TicketRow.checkedOpen (id : TicketId) (org : OrgId) (requester : UserId)
    (subject : Subject) (inbound : EmailMessageId) (now : Instant) : Checked TicketRow :=
  TicketRow.checked (openFromEmail id org requester subject inbound now)

/-- A customer reply: `draft_customer_ok` discharges the invariant. -/
def MessageRow.checkedCustomer (id : MessageId) (t : Ticket) (who : Who)
    (body : BodyText) (now : Instant) (hr : who.role = .customer) : Checked MessageRow :=
  MessageRow.checked (draftMessage id t who body false now) (draft_customer_ok id t who body now hr)

/-- An agent note, internal or not: `draft_agent_ok`. -/
def MessageRow.checkedAgent (id : MessageId) (t : Ticket) (who : Who)
    (body : BodyText) (internal : Bool) (now : Instant) (hr : who.role = .agent) :
    Checked MessageRow :=
  MessageRow.checked (draftMessage id t who body internal now) (draft_agent_ok id t who body internal now hr)

end Helpdesk
