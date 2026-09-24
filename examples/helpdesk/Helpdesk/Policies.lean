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

`rule` is the meaning; `scope` is the same predicate LeanDB compiles.
Keep them identical. `OrgRow` has no instance: default deny. -/

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
    ReadAs HelpdeskDb me (List (Stored MessageRow)) := do
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

def get (α : Type) [Entity α] [Policy s P α] (id : LeanDb.Id α) :
    TxAs s me ε (Option (Stored α)) :=
  ⟨(·.head?) <$> Txn.liftRead (Read.all ((Policy.scope (s := s) me).where' fun r => r.id == id))⟩

def lookup (α : Type) [Entity α] [HasUnique α] [Policy s P α]
    (ix : Unique α) (key : Unique.Key ix) : TxAs s me ε (Option (Stored α)) :=
  ⟨do
    match ← Txn.liftRead (Read.lookup α ix key) with
    | none => pure none
    | some row =>
      if Policy.rule (s := s) (P := P) (α := α) me row then pure (some row) else pure none⟩

def insert? (α : Type) [Entity α] [HasUnique α] [HasForeignKey α]
    [Policy s P α] [WritePolicy s P α] (row : Checked α) (denied : ε) :
    TxAs s me ε (Except (InsertError α) (Stored α)) :=
  ⟨do
    if WritePolicy.admit (s := s) (P := P) (α := α) me row.val then
      (·.map Current.toStored) <$> Txn.insert α row
    else Txn.throw denied⟩

def insert (α : Type) [Entity α] [HasUnique α] [HasForeignKey α]
    [Policy s P α] [WritePolicy s P α] (row : Checked α) (denied : ε)
    (onInsert : InsertError α → ε) : TxAs s me ε (Stored α) := do
  match ← insert? α row denied with
  | .ok s => pure s
  | .error e => throw (onInsert e)

def update (α : Type) [Entity α] [HasUnique α] [HasForeignKey α]
    [Policy s P α] [WritePolicy s P α] (old : Stored α) (new : Checked α)
    (denied : ε) (onUpdate : UpdateError α → ε) : TxAs s me ε (Stored α) :=
  ⟨do
    if Policy.rule (s := s) (P := P) (α := α) me old &&
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
    ReadAs HelpdeskDb me (Option (Stored TicketRow)) :=
  ⟨Read.get TicketRow id⟩

/-- error: failed to synthesize instance of type class
  Policy HelpdeskDb Who OrgRow -/
#guard_msgs (substring := true) in
def sneakyOrg (me : Actor Who) : ReadAs HelpdeskDb me (List (Stored OrgRow)) :=
  ReadAs.all OrgRow

/-- error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.Actor` is marked as private -/
#guard_msgs (substring := true) in
def spoof (id : LeanDb.Id TicketRow) :
    ReadAs HelpdeskDb (⟨⟨UserId.ofNat! 1, OrgId.ofNat! 1, .agent⟩⟩ : Actor Who)
      (Option (Stored TicketRow)) :=
  ReadAs.get TicketRow id

end Helpdesk
