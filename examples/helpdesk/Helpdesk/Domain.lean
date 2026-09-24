/-
  The help-desk domain: tenants, roles, tickets, messages, and the rules
  about who may see or change which of them. Pure Lean. No HTTP, no SQL.

  Proofs here are about these functions. They are not theorems about the
  database: at the pinned LeanDB, `DbState` is empty in proofs (review H1).
-/
namespace Helpdesk

/-! ## Identities

Possessing a well-formed id grants nothing. Each id fits in a LeanDB
`Ref` (below 2^63), so storage never re-checks the bound. -/

structure OrgId where
  n : Nat
  lt : n < 2^63 := by decide
  deriving DecidableEq, Repr, BEq, Hashable

structure UserId where
  n : Nat
  lt : n < 2^63 := by decide
  deriving DecidableEq, Repr, BEq, Hashable

structure TicketId where
  n : Nat
  lt : n < 2^63 := by decide
  deriving DecidableEq, Repr, BEq, Hashable

structure MessageId where
  n : Nat
  lt : n < 2^63 := by decide
  deriving DecidableEq, Repr, BEq, Hashable

def OrgId.make (n : Nat) : Except String OrgId :=
  if h : n == 0 || n >= 2^63 then .error "org id must be between 1 and 2^63-1"
  else .ok ⟨n, by simp at h; omega⟩

def UserId.make (n : Nat) : Except String UserId :=
  if h : n == 0 || n >= 2^63 then .error "user id must be between 1 and 2^63-1"
  else .ok ⟨n, by simp at h; omega⟩

def TicketId.make (n : Nat) : Except String TicketId :=
  if h : n == 0 || n >= 2^63 then .error "ticket id must be between 1 and 2^63-1"
  else .ok ⟨n, by simp at h; omega⟩

def MessageId.make (n : Nat) : Except String MessageId :=
  if h : n == 0 || n >= 2^63 then .error "message id must be between 1 and 2^63-1"
  else .ok ⟨n, by simp at h; omega⟩

def OrgId.ofNat! (n : Nat) : OrgId :=
  if h : n < 2^63 then ⟨n, h⟩ else ⟨0, by decide⟩

def UserId.ofNat! (n : Nat) : UserId :=
  if h : n < 2^63 then ⟨n, h⟩ else ⟨0, by decide⟩

def TicketId.ofNat! (n : Nat) : TicketId :=
  if h : n < 2^63 then ⟨n, h⟩ else ⟨0, by decide⟩

def MessageId.ofNat! (n : Nat) : MessageId :=
  if h : n < 2^63 then ⟨n, h⟩ else ⟨0, by decide⟩

instance : ToString OrgId := ⟨fun o => toString o.n⟩
instance : ToString UserId := ⟨fun u => toString u.n⟩
instance : ToString TicketId := ⟨fun t => toString t.n⟩
instance : ToString MessageId := ⟨fun m => toString m.n⟩

/-! ## Vocabulary -/

/-- Two kinds of actor sharing the same tables. -/
inductive Role where
  | agent
  | customer
  deriving Repr, DecidableEq, BEq

/-- `closed` is final. The only legal steps are `open → pending → solved → closed`. -/
inductive TicketStatus where
  | open
  | pending
  | solved
  | closed
  deriving Repr, DecidableEq, BEq

/-- Unix seconds, UTC. Bounded so a SQLite INTEGER can hold it. -/
structure Instant where
  unixSeconds : Nat
  lt : unixSeconds < 2^63 := by decide
  deriving DecidableEq, Repr, BEq

def Instant.make (n : Nat) : Except String Instant :=
  if h : n < 2^63 then .ok ⟨n, h⟩ else .error "instant is out of range"

def Instant.ofUnix! (n : Nat) : Instant :=
  if h : n < 2^63 then ⟨n, h⟩ else ⟨0, by decide⟩

/-- A ticket subject: trimmed, nonempty, at most 200 characters. -/
structure Subject where
  raw : String
  deriving Repr, DecidableEq, BEq

def Subject.make (s : String) : Except String Subject :=
  let t := s.trimAscii.toString
  if t.isEmpty then .error "subject must be nonempty"
  else if t.length > 200 then .error "subject must be at most 200 characters"
  else .ok ⟨t⟩

/-- A message body: trimmed, nonempty, at most 4000 characters. -/
structure BodyText where
  raw : String
  deriving Repr, DecidableEq, BEq

def BodyText.make (s : String) : Except String BodyText :=
  let t := s.trimAscii.toString
  if t.isEmpty then .error "body must be nonempty"
  else if t.length > 4000 then .error "body must be at most 4000 characters"
  else .ok ⟨t⟩

/-- An inbound `Message-ID`: trimmed, nonempty, at most 200 characters. -/
structure EmailMessageId where
  raw : String
  deriving Repr, DecidableEq, BEq

def EmailMessageId.make (s : String) : Except String EmailMessageId :=
  let t := s.trimAscii.toString
  if t.isEmpty then .error "Message-ID must be nonempty"
  else if t.length > 200 then .error "Message-ID must be at most 200 characters"
  else .ok ⟨t⟩

/-- The authenticated principal: one org, one role. -/
structure Who where
  user : UserId
  org : OrgId
  role : Role
  deriving DecidableEq, Repr, BEq

/-! ## State -/

structure Ticket where
  id : TicketId
  org : OrgId
  requester : UserId
  subject : Subject
  status : TicketStatus
  inboundId : EmailMessageId
  openedAt : Instant
  deriving DecidableEq, Repr

structure Message where
  id : MessageId
  org : OrgId
  ticket : TicketId
  author : UserId
  /-- The ticket's requester, stored on the message so the policy is
      single-table. -/
  requester : UserId
  /-- The author's role at write time, stored on the row so a customer
      can never be recorded as the author of an internal note. -/
  authorRole : Role
  body : BodyText
  internal : Bool
  createdAt : Instant
  deriving DecidableEq, Repr

/-! ## The rules (the meaning of the policies)

Declared once. The database view's `Policy.rule` is the same function,
applied to a stored row. -/

/-- Who may see a ticket: agents, every ticket in their org; customers,
    only tickets they opened, and only in their org. -/
def seesTicket (who : Who) (t : Ticket) : Bool :=
  decide (who.org = t.org) &&
    match who.role with
    | .agent => true
    | .customer => decide (who.user = t.requester)

/-- Who may see a message: the ticket rule, plus customers never see an
    internal note. Org and requester live on the message, so this does
    not join. -/
def seesMessage (who : Who) (m : Message) : Bool :=
  decide (who.org = m.org) &&
    match who.role with
    | .agent => true
    | .customer => decide (who.user = m.requester) && !m.internal

/-- The thread as `who` is allowed to see it. -/
def threadFor (who : Who) (ms : List Message) : List Message :=
  ms.filter (seesMessage who)

/-- Who may post: must see the ticket, the ticket must not be closed,
    and a customer cannot post an internal note. -/
def mayPost (who : Who) (t : Ticket) (internal : Bool) : Bool :=
  seesTicket who t && decide (t.status ≠ .closed) &&
    match who.role with
    | .agent => true
    | .customer => !internal

/-- The next status, or none if the ticket is already closed. -/
def nextStatus : TicketStatus → Option TicketStatus
  | .open => some .pending
  | .pending => some .solved
  | .solved => some .closed
  | .closed => none

/-- Who may advance a ticket one step along the lifecycle. -/
def mayAdvance (who : Who) (t : Ticket) : Bool :=
  decide (who.role = .agent) && seesTicket who t && (nextStatus t.status).isSome

def advanceTicket (t : Ticket) : Except Unit Ticket :=
  match nextStatus t.status with
  | none => .error ()
  | some s => .ok { t with status := s }

def openFromEmail (id : TicketId) (org : OrgId) (requester : UserId)
    (subject : Subject) (inbound : EmailMessageId) (now : Instant) : Ticket :=
  { id, org, requester, subject, status := .open, inboundId := inbound, openedAt := now }

def draftMessage (id : MessageId) (t : Ticket) (who : Who) (body : BodyText)
    (internal : Bool) (now : Instant) : Message :=
  { id, org := t.org, ticket := t.id, author := who.user, requester := t.requester,
    authorRole := who.role, body, internal, createdAt := now }

/-- A stored message is well-formed: a customer is never the author of
    an internal note. -/
def Message.ok (m : Message) : Prop :=
  m.authorRole = .customer → m.internal = false

/-! ## Theorems

These are the proofs. They are about the functions above, not about
SQLite. -/

theorem closed_is_final : nextStatus .closed = none := rfl

theorem nextStatus_some_not_closed {s s' : TicketStatus}
    (h : nextStatus s = some s') : s ≠ .closed := by
  cases s <;> simp [nextStatus] at h ⊢

theorem advance_refuses_closed (t : Ticket) (h : t.status = .closed) :
    advanceTicket t = .error () := by
  simp [advanceTicket, h, nextStatus]

theorem advance_not_from_closed {t t' : Ticket}
    (h : advanceTicket t = .ok t') : t.status ≠ .closed := by
  unfold advanceTicket at h
  cases hs : t.status <;> simp [nextStatus, hs] at h ⊢

theorem openFromEmail_open (id : TicketId) (org : OrgId) (requester : UserId)
    (subject : Subject) (inbound : EmailMessageId) (now : Instant) :
    (openFromEmail id org requester subject inbound now).status = .open := rfl

theorem seesTicket_same_org (who : Who) (t : Ticket)
    (h : seesTicket who t = true) : who.org = t.org := by
  simp [seesTicket, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem seesMessage_same_org (who : Who) (m : Message)
    (h : seesMessage who m = true) : who.org = m.org := by
  simp [seesMessage, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem customer_sees_own_ticket (who : Who) (t : Ticket)
    (hr : who.role = .customer) (h : seesTicket who t = true) :
    who.user = t.requester := by
  simp [seesTicket, hr, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

theorem customer_never_sees_internal (who : Who) (m : Message)
    (hr : who.role = .customer) (h : seesMessage who m = true) :
    m.internal = false := by
  simp [seesMessage, hr, Bool.and_eq_true, decide_eq_true_eq] at h
  cases hi : m.internal
  · rfl
  · simp [hi] at h

theorem customer_sees_own_message (who : Who) (m : Message)
    (hr : who.role = .customer) (h : seesMessage who m = true) :
    who.user = m.requester := by
  simp [seesMessage, hr, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.1

private theorem threadFor_mem {who : Who} {ms : List Message} {m : Message} :
    m ∈ threadFor who ms → seesMessage who m = true := by
  intro h
  simp [threadFor, List.mem_filter] at h
  exact h.2

theorem customer_thread_no_internal (who : Who) (ms : List Message)
    (hr : who.role = .customer) :
    ∀ m ∈ threadFor who ms, m.internal = false := by
  intro m hm
  exact customer_never_sees_internal who m hr (threadFor_mem hm)

theorem customer_thread_same_org (who : Who) (ms : List Message) :
    ∀ m ∈ threadFor who ms, m.org = who.org := by
  intro m hm
  exact (seesMessage_same_org who m (threadFor_mem hm)).symm

theorem customer_thread_own (who : Who) (ms : List Message)
    (hr : who.role = .customer) :
    ∀ m ∈ threadFor who ms, m.requester = who.user := by
  intro m hm
  exact (customer_sees_own_message who m hr (threadFor_mem hm)).symm

theorem other_org_invisible_ticket (who : Who) (t : Ticket)
    (h : who.org ≠ t.org) : seesTicket who t = false := by
  simp [seesTicket, decide_eq_false h]

theorem other_org_invisible_message (who : Who) (m : Message)
    (h : who.org ≠ m.org) : seesMessage who m = false := by
  simp [seesMessage, decide_eq_false h]

theorem mayPost_implies_sees (who : Who) (t : Ticket) (internal : Bool)
    (h : mayPost who t internal = true) : seesTicket who t = true := by
  simp [mayPost, Bool.and_eq_true] at h
  exact h.1.1

theorem mayPost_same_org (who : Who) (t : Ticket) (internal : Bool)
    (h : mayPost who t internal = true) : who.org = t.org :=
  seesTicket_same_org who t (mayPost_implies_sees who t internal h)

theorem mayPost_not_closed (who : Who) (t : Ticket) (internal : Bool)
    (h : mayPost who t internal = true) : t.status ≠ .closed := by
  simp [mayPost, Bool.and_eq_true] at h
  exact h.1.2

theorem customer_never_posts_internal (who : Who) (t : Ticket)
    (hr : who.role = .customer) : mayPost who t true = false := by
  simp [mayPost, hr]

theorem closed_ticket_nobody_posts (who : Who) (t : Ticket) (internal : Bool)
    (h : t.status = .closed) : mayPost who t internal = false := by
  simp [mayPost, h]

theorem mayAdvance_agent (who : Who) (t : Ticket)
    (h : mayAdvance who t = true) : who.role = .agent := by
  simp [mayAdvance, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

theorem mayAdvance_not_closed (who : Who) (t : Ticket)
    (h : mayAdvance who t = true) : t.status ≠ .closed := by
  simp [mayAdvance, Bool.and_eq_true] at h
  have hs : (nextStatus t.status).isSome = true := h.2
  cases hs' : t.status <;> simp [nextStatus, hs'] at hs ⊢

theorem customer_never_advances (who : Who) (t : Ticket)
    (hr : who.role = .customer) : mayAdvance who t = false := by
  simp [mayAdvance, hr]

theorem draft_customer_ok (id : MessageId) (t : Ticket) (who : Who)
    (body : BodyText) (now : Instant) (_hr : who.role = .customer) :
    Message.ok (draftMessage id t who body false now) := by
  intro hrole
  simp [draftMessage]

theorem draft_agent_ok (id : MessageId) (t : Ticket) (who : Who)
    (body : BodyText) (internal : Bool) (now : Instant)
    (hr : who.role = .agent) :
    Message.ok (draftMessage id t who body internal now) := by
  intro hrole
  simp [draftMessage, hr] at hrole

end Helpdesk
