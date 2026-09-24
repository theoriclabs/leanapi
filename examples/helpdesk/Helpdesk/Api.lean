/-
  The help-desk HTTP surface. Each endpoint's type is the spec: who may
  call it, what it reads or writes, and how it can fail. Handlers do not
  re-check org or internal-note rules; those are the policies.
-/
import Helpdesk.Policies
import LeanApi.Auth.Tokens

namespace Helpdesk

open LeanApi Lean LeanDb PolicyView

/-! ## Boundary types -/

instance : SmartCtor OrgId Nat := ⟨OrgId.make, (·.n)⟩
instance : SmartCtor UserId Nat := ⟨UserId.make, (·.n)⟩
instance : SmartCtor TicketId Nat := ⟨TicketId.make, (·.n)⟩
instance : SmartCtor Subject String := ⟨Subject.make, (·.raw)⟩
instance : SmartCtor BodyText String := ⟨BodyText.make, (·.raw)⟩
instance : SmartCtor EmailMessageId String := ⟨EmailMessageId.make, (·.raw)⟩
instance : SmartCtor Instant Nat := ⟨Instant.make, (·.unixSeconds)⟩

def Instant.ofNow (n : Now) : Instant := Instant.ofUnix! n.val

structure TicketView where
  id : Nat
  requester : Nat
  subject : String
  status : String
  openedAt : Nat
  deriving ToJson

structure MessageView where
  id : Nat
  author : Nat
  body : String
  internal : Bool
  createdAt : Nat
  deriving ToJson

structure TicketDetail where
  ticket : TicketView
  messages : List MessageView
  deriving ToJson

def ticketView (t : Ticket) : TicketView :=
  ⟨t.id.n, t.requester.n, t.subject.raw, ClosedEnum.encodeName t.status, t.openedAt.unixSeconds⟩

def messageView (m : Message) : MessageView :=
  ⟨m.id.n, m.author.n, m.body.raw, m.internal, m.createdAt.unixSeconds⟩

structure ReplyBody where
  body : BodyText
  internal : Bool

instance : FromBody ReplyBody :=
  FromBody.record (ReplyBody.mk <$> Fields.req "body" <*> Fields.dflt "internal" false)

structure InboundBody where
  messageId : EmailMessageId
  requester : UserId
  subject : Subject
  body : BodyText

instance : FromBody InboundBody :=
  FromBody.record (InboundBody.mk <$> Fields.req "messageId" <*> Fields.req "requester" <*>
    Fields.req "subject" <*> Fields.req "body")

inductive InboundResult where
  | created (t : Created TicketView)
  | existing (t : TicketView)

instance : ToResponse InboundResult where
  toRes
    | .created c => ToResponse.toRes c
    | .existing t => ToResponse.toRes t

/-! ## Failures -/

inductive HelpError where
  /-- Not visible, or missing: the same 404. -/
  | hidden
  /-- Visible, but this write is not allowed. -/
  | forbidden
  /-- The ticket is closed. -/
  | closed
  | unknownRequester

instance : ToProblem HelpError where
  status
    | .hidden => ⟨404, by decide⟩
    | .forbidden => ⟨403, by decide⟩
    | .closed => ⟨409, by decide⟩
    | .unknownRequester => ⟨422, by decide⟩
  detail
    | .hidden => none
    | .forbidden => some "not allowed"
    | .closed => some "ticket is closed"
    | .unknownRequester => some "unknown requester"

/-! ## Auth -/

def userWho (s : Stored UserRow) : Who :=
  ⟨uid s.id, oid s.val.org, s.val.role⟩

def tokenWho (t : String) : Read HelpdeskDb (Option Who) :=
  (·.map userWho) <$> Read.lookup UserRow UserRow.Unique.byToken (Tokens.digest t)

instance helpdeskAuth : AuthenticatesDb HelpdeskDb Who :=
  AuthenticatesDb.sessions tokenWho (realm := "helpdesk")

/-! ## Endpoints -/

/-- Tickets this actor may see. -/
def listTickets (me : Auth Who) : Read HelpdeskDb (List TicketView) :=
  ReadAs.forAuth me fun _ => do
    let rows ← ReadAs.all TicketRow
    return rows.map fun s => ticketView (reconstructTicket s.toStored)

/-- One ticket and its visible messages. Someone else's ticket is a 404. -/
def readTicket (me : Auth Who) (id : Path TicketId) :
    Read HelpdeskDb (Except HelpError TicketDetail) :=
  ReadAs.forAuth me fun a => do
    match ← ReadAs.get TicketRow (tref id.val) with
    | none => return .error .hidden
    | some s =>
      let t := reconstructTicket s
      let ms ← messagesOn a s.id
      return .ok ⟨ticketView t, ms.map fun m => messageView (reconstructMessage m.toStored)⟩

/-- Reply on a ticket. Customers cannot post internal notes; nobody
    writes to a closed ticket. -/
def postMessage (me : Auth Who) (id : Path TicketId) (body : Body ReplyBody) (now : Now) :
    Tx HelpdeskDb HelpError (Created MessageView) :=
  TxAs.forAuth me fun who => do
    match ← TxAs.get TicketRow (tref id.val) with
    | none => TxAs.throw .hidden
    | some s =>
      let t := reconstructTicket s
      let internal := body.val.internal
      if mayPost who t internal then
        let checked :=
          match hrole : who.role with
          | .customer => MessageRow.checkedCustomer (MessageId.ofNat! 0) t who body.val.body (Instant.ofNow now) hrole
          | .agent => MessageRow.checkedAgent (MessageId.ofNat! 0) t who body.val.body internal (Instant.ofNow now) hrole
        let row ← TxAs.insert MessageRow checked .forbidden fun
          | .missingRef _ => HelpError.hidden
          | .duplicate ix _ => nomatch ix
        pure ⟨messageView (reconstructMessage row), some s!"/tickets/{t.id.n}/messages"⟩
      else if t.status = .closed then TxAs.throw .closed
      else TxAs.throw .forbidden

/-- Agents advance `open → pending → solved → closed`. `closed` is final. -/
def advanceTicketEp (me : Auth Who) (id : Path TicketId) :
    Tx HelpdeskDb HelpError TicketView :=
  TxAs.forAuth me fun who => do
    match ← TxAs.get TicketRow (tref id.val) with
    | none => TxAs.throw .hidden
    | some s =>
      let t := reconstructTicket s
      if mayAdvance who t then
        match advanceTicket t with
        | .error _ => TxAs.throw .closed
        | .ok t' =>
          let _ ← TxAs.update TicketRow s (TicketRow.checked t') .forbidden fun
            | .stale _ | .gone | .missingRef _ | .duplicate _ _ => HelpError.hidden
          pure (ticketView t')
      else if t.status = .closed then TxAs.throw .closed
      else TxAs.throw .forbidden

/-- Inbound email. The same `(org, Message-ID)` creates one ticket. -/
def inbound (me : Auth Who) (body : Body InboundBody) (now : Now) :
    Tx HelpdeskDb HelpError InboundResult :=
  TxAs.forAuth me fun who =>
    match hrole : who.role with
    | .customer => TxAs.throw .forbidden
    | .agent => do
      let key := (oref who.org, body.val.messageId)
      match ← TxAs.lookup TicketRow TicketRow.Unique.byInbound key with
      | some s => pure (.existing (ticketView (reconstructTicket s)))
      | none =>
        match ← TxAs.get UserRow (uref body.val.requester) with
        | none => TxAs.throw .unknownRequester
        | some u =>
          if decide (u.val.role = .customer) && u.val.org == oref who.org then
            let draft := openFromEmail (TicketId.ofNat! 0) who.org (uid u.id) body.val.subject
              body.val.messageId (Instant.ofNow now)
            match ← TxAs.insert? TicketRow (TicketRow.checked draft) .forbidden with
            | .error (.duplicate ..) =>
              match ← TxAs.lookup TicketRow TicketRow.Unique.byInbound key with
              | some s => pure (.existing (ticketView (reconstructTicket s)))
              | none => TxAs.throw .hidden
            | .error (.missingRef _) => TxAs.throw .unknownRequester
            | .ok row =>
              let t := reconstructTicket row
              let _ ← TxAs.insert MessageRow
                (MessageRow.checkedAgent (MessageId.ofNat! 0) t who body.val.body false (Instant.ofNow now) hrole)
                .forbidden fun
                  | .missingRef _ => HelpError.hidden
                  | .duplicate ix _ => nomatch ix
              pure (.created ⟨ticketView t, some s!"/tickets/{t.id.n}"⟩)
          else TxAs.throw .unknownRequester

/-! ## The HTTP surface -/

def helpdeskApi : DbApi HelpdeskDb := api! [
  .get  "/tickets"                   listTickets,
  .get  "/tickets/{id:nat}"          readTicket,
  .post "/tickets/{id:nat}/messages" postMessage,
  .post "/tickets/{id:nat}/advance"  advanceTicketEp,
  .post "/inbound"                   inbound
]

def stack (log : String → IO Unit := IO.eprintln) : Stack :=
  Stack.of [recover log, requestId, accessLog log]

/-! ## Seed (trusted, unscoped): two orgs and four people -/

private def mustInsert (α : Type) [Entity α] [HasUnique α] [HasForeignKey α] [IsSchema.Has HelpdeskDb α]
    (v : α) : {σ : Type} → Txn σ HelpdeskDb String (Stored α) := do
  match Checked.check v with
  | .error _ => Txn.throw "seed row fails its invariant"
  | .ok c =>
    match ← Txn.insert α c with
    | .ok row => pure row.toStored
    | .error _ => Txn.throw "seed insert failed"

def seedTxn : {σ : Type} → Txn σ HelpdeskDb String Unit := do
  let acme ← mustInsert OrgRow ⟨"Acme"⟩
  let globex ← mustInsert OrgRow ⟨"Globex"⟩
  let _ ← mustInsert UserRow ⟨acme.id, "Ada", .agent, Tokens.digest "ada"⟩
  let _ ← mustInsert UserRow ⟨acme.id, "Carl", .customer, Tokens.digest "carl"⟩
  let _ ← mustInsert UserRow ⟨globex.id, "Gwen", .agent, Tokens.digest "gwen"⟩
  let _ ← mustInsert UserRow ⟨globex.id, "Gina", .customer, Tokens.digest "gina"⟩
  pure ()

def seed (conn : Conn) : IO Unit := do
  match ← DbM.run conn (Txn.run (s := HelpdeskDb) (ε := String) seedTxn) with
  | .ok (.ok (.ok ())) => pure ()
  | .ok (.ok (.error e)) => throw (IO.userError e)
  | .ok (.error f) => throw (IO.userError s!"seed fault: {f}")
  | .error e => throw (IO.userError s!"seed: {e}")

end Helpdesk
