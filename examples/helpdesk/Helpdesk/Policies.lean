/-
  Row-level policies for the help desk, and a write view in the same
  pattern as PolicyView (private constructors, default deny, the rule
  pushed into SQL).

  `PolicyView.Actor.mk` is module-private, so the write view is indexed by
  `Who` and entered through `TxAs.forAuth` from the request's `Auth`.
  Forging `Auth` is the same framework caveat PolicyView documents.
-/
import PolicyView.Policy
import Helpdesk.Schema
import LeanApi.Http.DbEndpoint

namespace Helpdesk

open LeanDb PolicyView LeanApi

/-! ## Read policies: the domain rules, as SQL

`rule` is a copy of `seesTicket` / `seesMessage` on stored rows; `scope`
is a third copy that LeanDB compiles. They are written by hand.
`OrgRow` has no instance: default deny. -/

instance : Policy HelpdeskDb Who TicketRow where
  rule who t :=
    t.val.org == oref who.org &&
      (who.role == Role.agent || t.val.requester == uref who.user)
  scope who :=
    (Query.from TicketRow).where' fun t =>
      t.val.org == oref who.org &&
        (who.role == Role.agent || t.val.requester == uref who.user)

instance : Policy HelpdeskDb Who MessageRow where
  rule who m :=
    m.val.org == oref who.org &&
      (who.role == Role.agent ||
        (m.val.requester == uref who.user && m.val.internal == false))
  scope who :=
    (Query.from MessageRow).where' fun m =>
      m.val.org == oref who.org &&
        (who.role == Role.agent ||
          (m.val.requester == uref who.user && m.val.internal == false))

instance : Policy HelpdeskDb Who UserRow where
  rule who u :=
    u.val.org == oref who.org &&
      (who.role == Role.agent || u.id == uref who.user)
  scope who :=
    (Query.from UserRow).where' fun u =>
      u.val.org == oref who.org &&
        (who.role == Role.agent || u.id == uref who.user)

/-- The SQL filter a scoped ticket `get` sends (for display and tests). -/
def ticketGetSql (who : Who) (id : LeanDb.Id TicketRow) : String × Array Col :=
  ((Policy.scope (s := HelpdeskDb) who).where' fun (t : Stored TicketRow) => t.id == id).pred.renderT

/-- Messages of one ticket: the policy is in SQL (`ReadAs.all`); the ticket
    id is filtered in Lean. PolicyView.ReadAs has no `filter` yet. -/
def messagesOn (me : Actor Who) (tid : LeanDb.Id TicketRow) :
    ReadAs HelpdeskDb me (List (LeanDb.Valid MessageRow)) := do
  let ms ← ReadAs.all MessageRow
  return ms.filter (fun m => m.val.ticket == tid)

/-! ## Write policy: WITH CHECK

Inserts and updates must produce a row the actor is allowed to write.
Closed tickets are a domain check (`mayPost`), not a column on the
message: the handler reads the ticket through the view first. -/

class WritePolicy (s : Type) [IsSchema s] (P : Type) (α : Type) [Entity α] where
  admit : P → α → Bool

instance : WritePolicy HelpdeskDb Who TicketRow where
  admit who t := who.role == Role.agent && t.org == oref who.org

instance : WritePolicy HelpdeskDb Who MessageRow where
  admit who m :=
    m.org == oref who.org && m.author == uref who.user &&
      (who.role == Role.agent ||
        (m.requester == uref who.user && m.internal == false && who.role == Role.customer))

/-! ## Domain functions vs `rule` / `admit`

`rule` and `sees*` are two copies. A stored `Ref` that `== oref o`
reconstructs to `o`; the converse can fail for a negative id, so these
are implications (policy admits ⇒ domain true), not equalities.
`scope` is a third copy; it is not proved equal to `rule`.

`WritePolicy.admit` does not see ticket status, so it is not `mayPost` /
`mayAdvance`. It implies the visibility rule plus (for tickets) that the
actor is an agent. On a row mapped *from* the domain, `mayPost` /
`mayAdvance` imply `admit`. -/

theorem ticket_rule_implies_seesTicket (who : Who) (t : Stored TicketRow)
    (h : Policy.rule (s := HelpdeskDb) (P := Who) (α := TicketRow) who t = true) :
    seesTicket who (reconstructTicket t) = true := by
  have hrule :
      (t.val.org == oref who.org &&
        (who.role == Role.agent || t.val.requester == uref who.user)) = true := h
  rw [Bool.and_eq_true] at hrule
  have horg := beq_oref_implies_oid t.val.org who.org hrule.1
  unfold seesTicket reconstructTicket TicketRow.toTicket
  simp [horg]
  cases hagent : (who.role == Role.agent)
  · have hcust := role_eq_customer_of_not_agent (role_ne_agent_of_beq_false hagent)
    have req : (t.val.requester == uref who.user) = true := by
      simpa [hagent] using hrule.2
    have huser := beq_uref_implies_uid t.val.requester who.user req
    simp [hcust, huser]
  · have ha := role_eq_agent_of_beq hagent
    simp [ha]

theorem message_rule_implies_seesMessage (who : Who) (m : Stored MessageRow)
    (h : Policy.rule (s := HelpdeskDb) (P := Who) (α := MessageRow) who m = true) :
    seesMessage who (reconstructMessage m) = true := by
  have hrule :
      (m.val.org == oref who.org &&
        (who.role == Role.agent ||
          (m.val.requester == uref who.user && m.val.internal == false))) = true := h
  rw [Bool.and_eq_true] at hrule
  have horg := beq_oref_implies_oid m.val.org who.org hrule.1
  unfold seesMessage reconstructMessage MessageRow.toMessage
  simp [horg]
  cases hagent : (who.role == Role.agent)
  · have hcust := role_eq_customer_of_not_agent (role_ne_agent_of_beq_false hagent)
    have hrest : (m.val.requester == uref who.user && m.val.internal == false) = true := by
      simpa [hagent] using hrule.2
    rw [Bool.and_eq_true] at hrest
    have huser := beq_uref_implies_uid m.val.requester who.user hrest.1
    have hpub : m.val.internal = false := eq_of_beq hrest.2
    simp [hcust, huser, hpub]
  · have ha := role_eq_agent_of_beq hagent
    simp [ha]

theorem ticket_admit_implies_agent (who : Who) (t : TicketRow)
    (h : WritePolicy.admit (s := HelpdeskDb) (P := Who) (α := TicketRow) who t = true) :
    who.role = .agent := by
  have hadm : (who.role == Role.agent && t.org == oref who.org) = true := h
  rw [Bool.and_eq_true] at hadm
  exact role_eq_agent_of_beq hadm.1

theorem ticket_admit_implies_seesTicket (who : Who) (t : TicketRow)
    (h : WritePolicy.admit (s := HelpdeskDb) (P := Who) (α := TicketRow) who t = true) :
    seesTicket who (t.toTicket ⟨0⟩) = true := by
  have hadm : (who.role == Role.agent && t.org == oref who.org) = true := h
  rw [Bool.and_eq_true] at hadm
  have ha := role_eq_agent_of_beq hadm.1
  have horg := beq_oref_implies_oid t.org who.org hadm.2
  unfold seesTicket TicketRow.toTicket
  simp [ha, horg]

theorem message_admit_implies_seesMessage (who : Who) (m : MessageRow)
    (h : WritePolicy.admit (s := HelpdeskDb) (P := Who) (α := MessageRow) who m = true) :
    seesMessage who (m.toMessage ⟨0⟩) = true := by
  have hadm :
      (m.org == oref who.org && m.author == uref who.user &&
        (who.role == Role.agent ||
          (m.requester == uref who.user && m.internal == false &&
            who.role == Role.customer))) = true := h
  rw [Bool.and_eq_true] at hadm
  rw [Bool.and_eq_true] at hadm
  have horg := beq_oref_implies_oid m.org who.org hadm.1.1
  unfold seesMessage MessageRow.toMessage
  simp [horg]
  cases hagent : (who.role == Role.agent)
  · have hcust := role_eq_customer_of_not_agent (role_ne_agent_of_beq_false hagent)
    have hrest :
        (m.requester == uref who.user && m.internal == false &&
          who.role == Role.customer) = true := by
      simpa [hagent] using hadm.2
    rw [Bool.and_eq_true] at hrest
    rw [Bool.and_eq_true] at hrest
    have huser := beq_uref_implies_uid m.requester who.user hrest.1.1
    have hpub : m.internal = false := eq_of_beq hrest.1.2
    simp [hcust, huser, hpub]
  · have ha := role_eq_agent_of_beq hagent
    simp [ha]

theorem mayAdvance_implies_ticket_admit (who : Who) (t : Ticket)
    (h : mayAdvance who t = true) :
    WritePolicy.admit (s := HelpdeskDb) (P := Who) (α := TicketRow) who
      (TicketRow.ofTicket t) = true := by
  have ha := mayAdvance_agent who t h
  have hsees : seesTicket who t = true := by
    simp [mayAdvance, Bool.and_eq_true] at h
    exact h.1.2
  have horg := seesTicket_same_org who t hsees
  change ((who.role == Role.agent) && ((TicketRow.ofTicket t).org == oref who.org)) = true
  simp [ha, TicketRow.ofTicket, oref_beq_of_eq horg.symm, role_beq_agent]

theorem mayPost_implies_message_admit (id : MessageId) (t : Ticket) (who : Who)
    (body : BodyText) (internal : Bool) (now : Instant)
    (h : mayPost who t internal = true) :
    WritePolicy.admit (s := HelpdeskDb) (P := Who) (α := MessageRow) who
      (MessageRow.ofMessage (draftMessage id t who body internal now)) = true := by
  have hsees := mayPost_implies_sees who t internal h
  have horg := seesTicket_same_org who t hsees
  change
    ((oref t.org == oref who.org) && (uref who.user == uref who.user) &&
      ((who.role == Role.agent) ||
        ((uref t.requester == uref who.user) && (internal == false) &&
          (who.role == Role.customer)))) = true
  simp only [oref_beq_of_eq horg.symm, uref_beq_self, Bool.and_true]
  cases hagent : (who.role == Role.agent)
  · have hcust := role_eq_customer_of_not_agent (role_ne_agent_of_beq_false hagent)
    have huser := customer_sees_own_ticket who t hcust hsees
    have hpub : internal = false := by
      simp [mayPost, hcust, Bool.and_eq_true] at h
      cases hi : internal
      · rfl
      · simp [hi] at h
    simp [uref_beq_of_eq huser.symm, hpub, hcust, role_beq_customer]
  · simp

/-! ## Write view

Private constructor: an unscoped `Txn` cannot be put into the view.
Every get/insert/update applies the table's read policy and write check. -/

structure TxAs (s : Type) [IsSchema s] {P : Type} (me : P) (ε α : Type) : Type 1 where
  private mk ::
  prog : {σ : Type} → Txn σ s ε α

namespace TxAs
variable {s : Type} [IsSchema s] {P : Type} {me : P} {ε : Type}

instance : Monad (TxAs s me ε) where
  pure a := ⟨pure a⟩
  bind m f := ⟨m.prog >>= fun a => (f a).prog⟩

def throw (e : ε) : TxAs s me ε α := ⟨Txn.throw e⟩

def get (α : Type) [Entity α] [IsSchema.Has s α] [Policy s P α] (id : LeanDb.Id α) :
    TxAs s me ε (Option (LeanDb.Valid α)) :=
  ⟨(·.head?) <$> Txn.liftRead (Read.all (s := s) ((Policy.scope (s := s) (α := α) me).where' fun r => r.id == id))⟩

def lookup (α : Type) [Entity α] [HasUnique α] [IsSchema.Has s α] [Policy s P α]
    (ix : Unique α) (key : Unique.Key ix) : TxAs s me ε (Option (LeanDb.Valid α)) :=
  ⟨do
    match ← Txn.liftRead (Read.lookup α ix key) with
    | none => pure none
    | some row =>
      if Policy.rule (s := s) (P := P) (α := α) me row.toStored then pure (some row) else pure none⟩

def insert? (α : Type) [Entity α] [HasUnique α] [HasForeignKey α] [IsSchema.Has s α]
    [Policy s P α] [WritePolicy s P α] (row : Checked α) (denied : ε) :
    TxAs s me ε (Except (InsertError α) (Stored α)) :=
  ⟨do
    if WritePolicy.admit (s := s) (P := P) (α := α) me row.val then
      (·.map Current.toStored) <$> Txn.insert α row
    else Txn.throw denied⟩

def insert (α : Type) [Entity α] [HasUnique α] [HasForeignKey α] [IsSchema.Has s α]
    [Policy s P α] [WritePolicy s P α] (row : Checked α) (denied : ε)
    (onInsert : InsertError α → ε) : TxAs s me ε (Stored α) := do
  match ← insert? α row denied with
  | .ok s => pure s
  | .error e => throw (onInsert e)

def update (α : Type) [Entity α] [HasUnique α] [HasForeignKey α] [IsSchema.Has s α]
    [Policy s P α] [WritePolicy s P α] (old : LeanDb.Valid α) (new : Checked α)
    (denied : ε) (onUpdate : UpdateError α → ε) : TxAs s me ε (Stored α) :=
  ⟨do
    if Policy.rule (s := s) (P := P) (α := α) me old.toStored &&
        WritePolicy.admit (s := s) (P := P) (α := α) me new.val then
      match ← Txn.update α old new with
      | .ok row => pure row
      | .error e => Txn.throw (onUpdate e)
    else Txn.throw denied⟩

/-- Bridge for `DbApi` handlers: the request's `Auth` is the only `Who`
    the write program is indexed by. -/
def forAuth {ε α : Type} (me : Auth Who)
    (prog : (who : Who) → TxAs HelpdeskDb who ε α) : Tx HelpdeskDb ε α :=
  (prog me.val).prog

end TxAs

/-! ## What the view refuses, at compile time -/

/-- error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.ReadAs` is marked as private -/
#guard_msgs (substring := true) in
def sneakyRead (me : Actor Who) (id : LeanDb.Id TicketRow) :
    ReadAs HelpdeskDb me (Option (LeanDb.Valid TicketRow)) :=
  ⟨Read.get TicketRow id⟩

/-- error: failed to synthesize instance of type class
  Policy HelpdeskDb Who OrgRow -/
#guard_msgs (substring := true) in
def sneakyOrg (me : Actor Who) : ReadAs HelpdeskDb me (List (LeanDb.Valid OrgRow)) :=
  ReadAs.all OrgRow

/-- error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.Actor` is marked as private -/
#guard_msgs (substring := true) in
def spoof (id : LeanDb.Id TicketRow) :
    ReadAs HelpdeskDb (⟨⟨UserId.ofNat! 1, OrgId.ofNat! 1, .agent⟩⟩ : Actor Who)
      (Option (LeanDb.Valid TicketRow)) :=
  ReadAs.get TicketRow id

end Helpdesk
