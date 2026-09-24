/-
  Row-level policies and a column-level projection, following
  `examples/policy-view`. `import PolicyView.Policy`; that module is not
  modified.

  What this file adds:
  - `Policy` instances (default deny for any table without one).
    `rule` is proved equal to `Booking.visibleTo` through `reconstruct`;
    `scope` is the same predicate written as SQL and is not yet proved
    to match `rule`.
  - `Project` / `ProjRead`: a different row type for free/busy, defined
    as `BusyInterval.ofInterval ∘ Booking.interval ∘ reconstruct`.
    Mapping it over stored rows is `freeBusy` of the corresponding
    bookings. LeanDB still `SELECT`s the entity (no column-restricted
    SELECT yet); pushing the projection into SQL is planned with
    DESIGN §7.5.
  - `WritePolicy` / `TxnAs`: insert only when the actor is admitted, and
    delete only a row already read through the view. `admits` is proved
    equal to "the actor is the invitee" through `ofBooking`.
-/
import PolicyView.Policy
import Scheduling.Schema

open LeanDb PolicyView

namespace Scheduling

/-! ## Policies

`rule` is the Lean predicate proofs talk about. `scope` is the SQL query,
written again by hand. They are not yet proved equal (`policy%` / DESIGN
§7.5). `rule` *is* proved equal to the domain's `visibleTo` through the
row mapping, below. -/

/-- Booking details: host or invitee. Both ids sit on the row (single-table). -/
instance : Policy Calendar PersonId BookingRow where
  rule p r := r.val.host == pref p || r.val.invitee == pref p
  scope p := (LeanDb.Query.from BookingRow).where' fun r =>
    r.val.host == pref p || r.val.invitee == pref p

/-- Published openings are public: booking has to look them up. The private
    data is on `BookingRow`, not here. -/
instance : Policy Calendar PersonId AvailabilityRow where
  rule _ _ := true
  scope _ := LeanDb.Query.from AvailabilityRow

/-- Who may insert a row. Separate from the read policy (Postgres
    `WITH CHECK` vs `USING`). -/
class WritePolicy (s : Type) [IsSchema s] (P : Type) (α : Type) [Entity α] where
  admits : P → α → Bool

/-- An invitee books; they become the stored invitee. -/
instance : WritePolicy Calendar PersonId BookingRow where
  admits p r := r.invitee == pref p

/-- A host publishes their own openings. -/
instance : WritePolicy Calendar PersonId AvailabilityRow where
  admits p r := r.host == pref p

/-! ## Column-level projection

`BusyInterval` holds the interval only. A `ProjRead` program cannot be
built from an unscoped `Read` (private constructor), so a handler that
goes through it never binds title, notes or invitee. -/

class Project (α β : Type) [Entity α] where
  project : Stored α → β

/-- The free/busy column: `interval` of the reconstructed booking, not a
    handler-side filter. Equal to `Booking.toBusy` (`project_eq_toBusy`). -/
instance : Project BookingRow BusyInterval where
  project s := BusyInterval.ofInterval (reconstruct s).interval

structure ProjRead (s : Type) [IsSchema s] (β : Type) : Type 1 where
  private mk ::
  prog : Read s (List β)

/-- Busy intervals of this host. The query filters on `host` (on the row);
    `Project` drops every other column from the type. -/
def BookingRow.busyOf (host : PersonId) : LeanDb.Query Calendar [BookingRow] (Stored BookingRow) :=
  (LeanDb.Query.from BookingRow).where' fun r => r.val.host == pref host

def ProjRead.busy (host : PersonId) : ProjRead Calendar BusyInterval :=
  ⟨(·.map (Project.project (α := BookingRow))) <$> Read.all (BookingRow.busyOf host)⟩

def ProjRead.toRead {s : Type} [IsSchema s] {β : Type} (p : ProjRead s β) : Read s (List β) :=
  p.prog

/-- SQL filter the busy query sends (for display). -/
def busySql (host : PersonId) : String × Array Col :=
  (BookingRow.busyOf host).pred.renderT

/-- The row with this id, if `p`'s read policy admits it. Policy and id go
    to SQL together. -/
def scopedGet (α : Type) [Entity α] {s P : Type} [IsSchema s] [Policy s P α]
    (p : P) (id : LeanDb.Id α) : Read s (Option (Stored α)) :=
  (·.head?) <$> Read.all ((Policy.scope (s := s) p).where' fun r => r.id == id)

/-! ## Write view

Parameterized by the actor value, not `PolicyView.Actor` (that constructor
lives in `PolicyView.Policy`). The private constructor still stops an
unscoped `Txn` being wrapped in. `Auth`'s constructor is private, so
`forAuth` acts for the authenticated caller and no one else. -/

structure TxnAs (σ : Type) (s : Type) [IsSchema s] {P : Type} (p : P)
    (ε : Type) (α : Type) : Type 1 where
  private mk ::
  prog : Txn σ s ε α

instance {σ s : Type} [IsSchema s] {P : Type} {p : P} {ε : Type} :
    Monad (TxnAs σ s p ε) where
  pure a := ⟨pure a⟩
  bind m f := ⟨m.prog >>= fun a => (f a).prog⟩

abbrev TxAs (s : Type) [IsSchema s] {P : Type} (p : P) (ε α : Type) :=
  {σ : Type} → TxnAs σ s p ε α

def TxAs.forAuth {s : Type} [IsSchema s] {P ε ρ : Type} (me : LeanApi.Auth P)
    (k : (p : P) → TxAs s p ε ρ) : LeanApi.Tx s ε ρ :=
  fun {_σ} => (k me.val).prog

namespace TxnAs
variable {σ : Type} {s : Type} [IsSchema s] {P : Type} {p : P} {ε : Type}

def liftRead (r : Read s α) : TxnAs σ s p ε α := ⟨Txn.liftRead r⟩

def throw (e : ε) : TxnAs σ s p ε α := ⟨Txn.throw e⟩

/-- The row with this id, if the read policy admits it. -/
def get (α : Type) [Entity α] [Policy s P α] (id : LeanDb.Id α) :
    TxnAs σ s p ε (Option (Stored α)) :=
  ⟨Txn.liftRead (scopedGet (s := s) α p id)⟩

/-- Insert only if the write policy admits the new row. `none` is denied. -/
def insert? (α : Type) [Entity α] [HasUnique α] [HasForeignKey α]
    [WritePolicy s P α] (v : Checked α) :
    TxnAs σ s p ε (Option (Except (InsertError α) (Current σ α))) :=
  if WritePolicy.admits (s := s) p v.val then
    ⟨some <$> Txn.insert α v⟩
  else
    ⟨pure none⟩

/-- Delete only a row already read through the view. `none` is hidden. -/
def deleteVisible (α : Type) [Entity α] [Policy s P α] [HasReferencedBy s α]
    (id : LeanDb.Id α) :
    TxnAs σ s p ε (Option (Except (DeleteError s α) (Stored α))) :=
  ⟨do
    match ← Txn.liftRead (scopedGet (s := s) α p id) with
    | none => pure none
    | some row => some <$> Txn.delete α row.id⟩

end TxnAs

/-! ## Policy and projection, tied to the domain

Pure equalities through `reconstruct` / `ofBooking`. Not theorems over
`DbState`. Foreign-key `Ref`s that LeanDB issues are non-negative, which
is the hypothesis on `bookingPolicy_rule_eq_visibleTo`. The implication
`bookingPolicy_rule_implies_visibleTo` does not need it. -/

/-- On a stored row whose host and invitee are non-negative ids, the
    booking policy is the domain's `visibleTo`. -/
theorem bookingPolicy_rule_eq_visibleTo (p : PersonId) (s : Stored BookingRow)
    (hh : 0 ≤ s.val.host.toInt64) (hi : 0 ≤ s.val.invitee.toInt64) :
    Policy.rule (s := Calendar) p s = Booking.visibleTo p (reconstruct s) := by
  simp only [Policy.rule, Booking.visibleTo, reconstruct, BookingRow.toBooking]
  rw [ref_beq_pref s.val.host p hh, ref_beq_pref s.val.invitee p hi]

/-- If the policy admits `p`, the corresponding booking is `visibleTo p`.
    No hypothesis on the stored refs: `pref p` always maps back to `p`. -/
theorem bookingPolicy_rule_implies_visibleTo (p : PersonId) (s : Stored BookingRow) :
    Policy.rule (s := Calendar) p s = true →
      Booking.visibleTo p (reconstruct s) = true := by
  simp only [Policy.rule, Booking.visibleTo, reconstruct, BookingRow.toBooking]
  intro h
  rcases Bool.or_eq_true_iff.mp h with hh | hi
  · simp [ref_beq_pref_implies_pid s.val.host p hh]
  · simp [ref_beq_pref_implies_pid s.val.invitee p hi]

/-- Through `ofBooking`: the write view admits the invitee, and only them. -/
theorem writePolicy_admits_ofBooking (p : PersonId) (b : Booking) :
    WritePolicy.admits (s := Calendar) p (BookingRow.ofBooking b) = (p == b.invitee) := by
  simp only [WritePolicy.admits, BookingRow.ofBooking]
  rw [ref_beq_pref (pref b.invitee) p (pref_nonneg b.invitee), pid_pref]

/-- Same fact on a stored row whose invitee id is non-negative. -/
theorem writePolicy_admits_eq_invitee (p : PersonId) (r : BookingRow)
    (h : 0 ≤ r.invitee.toInt64) :
    WritePolicy.admits (s := Calendar) p r = (p == pid r.invitee) := by
  simp only [WritePolicy.admits]
  exact ref_beq_pref r.invitee p h

/-- The projection of one stored row is `toBusy` of the reconstructed booking. -/
theorem project_eq_toBusy (s : Stored BookingRow) :
    Project.project (α := BookingRow) s = (reconstruct s).toBusy :=
  (toBusy_eq_ofInterval (reconstruct s)).symm

/-- `listBusy` maps this over the rows the query yields: that list is
    `freeBusy` of the corresponding bookings. -/
theorem project_list_eq_freeBusy (rows : List (Stored BookingRow)) :
    rows.map (Project.project (α := BookingRow)) = freeBusy (rows.map reconstruct) := by
  simp [Project.project, freeBusy, reconstruct, Booking.toBusy,
    BusyInterval.ofInterval, Booking.interval, Slot.interval, BusyInterval.ofSlot,
    BookingRow.toBooking, Slot.finish]

/-! ## What a foreign module cannot do is pinned in `Bypass.lean`.

Here, default deny for a table with no policy: `PersonRow` has no `Policy`. -/

/-- error: failed to synthesize instance of type class
  Policy Calendar PersonId PersonRow -/
#guard_msgs (substring := true) in
/-- Bypass: a table with no policy (everyone's token digests). -/
def sneakyPeople (me : Actor PersonId) : ReadAs Calendar me (List (Stored PersonRow)) :=
  ReadAs.all PersonRow

end Scheduling
