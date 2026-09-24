/-
  Scheduling over LeanDB programs: five routes.

  The type of each endpoint is the spec: who may call it (`Auth` or not),
  what it reads or writes (`Read` / `Tx`), and every way it can fail
  (`ScheduleError`).
-/
import LeanApi.Http.DbEndpoint
import Scheduling.Policies
import LeanApi.Auth.Tokens

namespace Scheduling

open LeanApi Lean LeanDb PolicyView

/-! ## Smart constructors: HTTP and columns share them -/

instance : SmartCtor Instant Nat := ⟨Instant.make, (·.unix)⟩
instance : SmartCtor PersonId Nat := ⟨PersonId.make, (·.n)⟩
instance : SmartCtor BookingId Nat := ⟨BookingId.make, (·.n)⟩
instance : SmartCtor Title String := ⟨Title.make, (·.raw)⟩
instance : SmartCtor Notes String := ⟨Notes.make, (·.raw)⟩
instance : SmartCtor Handle String := ⟨Handle.make, (·.raw)⟩
instance : SmartCtor Slot Instant := ⟨Slot.make, (·.start)⟩

/-! ## Actors -/

/-- A bearer token is a `PersonRow`, found by its digest. -/
def tokenPerson (t : String) : Read Calendar (Option PersonId) :=
  (·.map fun row => pid row.id) <$>
    Read.lookup PersonRow PersonRow.Unique.byDigest (Tokens.digest t)

instance calendarAuth : AuthenticatesDb Calendar PersonId :=
  AuthenticatesDb.sessions tokenPerson (realm := "calendar")

/-! ## Inputs -/

structure SlotBody where
  start : Slot

instance : FromBody SlotBody := .record (SlotBody.mk <$> .req "start")

structure BookBody where
  start : Slot
  title : Title
  notes : Notes

instance : FromBody BookBody :=
  .record (BookBody.mk <$> .req "start" <*> .req "title" <*> .dflt "notes" Notes.empty)

/-! ## Outputs -/

structure BusyIntervalView where
  start : Nat
  finish : Nat
  deriving ToJson

def BusyIntervalView.of (i : BusyInterval) : BusyIntervalView :=
  ⟨i.startUnix, i.finishUnix⟩

structure BusyCalendar where
  host : Nat
  busy : List BusyIntervalView
  deriving ToJson

structure BookingView where
  id : Nat
  host : Nat
  invitee : Nat
  start : Nat
  finish : Nat
  title : String
  notes : String
  deriving ToJson

def bookingView (b : Booking) : BookingView :=
  { id := b.id.n, host := b.host.n, invitee := b.invitee.n,
    start := b.slot.start.unix, finish := b.slot.finish.unix,
    title := b.title.raw, notes := b.notes.raw }

structure SlotView where
  host : Nat
  start : Nat
  finish : Nat
  deriving ToJson

/-! ## Failures -/

inductive ScheduleError where
  /-- Not yours, or no such row: the same answer (404). -/
  | hidden
  | inPast
  | notAvailable
  | taken
  | missingPerson

instance : ToProblem ScheduleError where
  status
    | .hidden => ⟨404, by decide⟩
    | .inPast | .missingPerson => ⟨422, by decide⟩
    | .notAvailable | .taken => ⟨409, by decide⟩
  detail
    | .hidden => none
    | .inPast => some "slot must start in the future"
    | .notAvailable => some "host has not published that slot"
    | .taken => some "that slot is already booked"
    | .missingPerson => some "unknown person"

/-! ## Endpoints -/

/-- Anyone: this host's busy intervals. Titles, notes and invitees are not
    in the result type; the program is a `ProjRead`. -/
def listBusy (host : Path PersonId) : Read Calendar BusyCalendar := do
  let busy ← ProjRead.toRead (ProjRead.busy host.val)
  pure { host := host.val.n, busy := busy.map BusyIntervalView.of }

/-- The host publishes an aligned future slot. -/
def publish (me : Auth PersonId) (host : Path PersonId) (body : Body SlotBody) (now : Now) :
    Tx Calendar ScheduleError (Created SlotView) :=
  TxAs.forAuth me fun p => fun {_σ} => do
    if p != host.val then TxnAs.throw .hidden
    else
      let nowI := Instant.ofNat! now.val
      match decidePublish nowI body.val.start with
      | .error .inPast => TxnAs.throw .inPast
      | .ok () =>
        match ← TxnAs.insert? AvailabilityRow (AvailabilityRow.checked
            { host := pref host.val, slot := body.val.start }) with
        | none => TxnAs.throw .hidden
        | some (.error (.duplicate .bySlot _)) => TxnAs.throw .taken
        | some (.error (.missingRef _)) => TxnAs.throw .missingPerson
        | some (.ok _) =>
          let s := body.val.start
          pure ⟨{ host := host.val.n, start := s.start.unix, finish := s.finish.unix },
            some s!"/hosts/{host.val.n}/availability"⟩

/-- An invitee books a published future slot. A clash is `BookingRow.bySlot`. -/
def book (me : Auth PersonId) (host : Path PersonId) (body : Body BookBody) (now : Now) :
    Tx Calendar ScheduleError (Created BookingView) :=
  TxAs.forAuth me fun p => fun {_σ} => do
    let nowI := Instant.ofNat! now.val
    let slot := body.val.start
    match ← TxnAs.liftRead (Read.lookup AvailabilityRow AvailabilityRow.Unique.bySlot
        (pref host.val, slot)) with
    | none => TxnAs.throw .notAvailable
    | some _ =>
      match decideBook nowI [slot] [] slot with
      | .error .inPast => TxnAs.throw .inPast
      | .error .notAvailable => TxnAs.throw .notAvailable
      | .error .taken => TxnAs.throw .taken
      | .ok () =>
        match ← TxnAs.insert? BookingRow (BookingRow.checked
            { host := pref host.val, invitee := pref p, slot,
              title := body.val.title, notes := body.val.notes }) with
        | none => TxnAs.throw .hidden
        | some (.error (.duplicate .bySlot _)) => TxnAs.throw .taken
        | some (.error (.missingRef _)) => TxnAs.throw .missingPerson
        | some (.ok cur) =>
          let b := reconstruct cur.toStored
          pure ⟨bookingView b, some s!"/bookings/{b.id.n}"⟩

/-- Details: host or invitee. Anyone else is indistinguishable from missing. -/
def readBooking (me : Auth PersonId) (id : Path BookingId) :
    Read Calendar (Except ScheduleError BookingView) :=
  ReadAs.forAuth me fun _a => do
    match ← ReadAs.get BookingRow (bidRef id.val) with
    | none => return .error .hidden
    | some s => return .ok (bookingView (reconstruct s))

/-- Cancel: host or invitee. Deleting the row frees the unique slot. -/
def cancelBooking (me : Auth PersonId) (id : Path BookingId) :
    Tx Calendar ScheduleError NoContent :=
  TxAs.forAuth me fun _p => fun {_σ} => do
    let r : Option (Except (DeleteError Calendar BookingRow) (Stored BookingRow)) ←
      TxnAs.deleteVisible BookingRow (bidRef id.val)
    match r with
    | none => TxnAs.throw .hidden
    | some (.error .gone) => TxnAs.throw .hidden
    | some (.error (.restricted w _)) => nomatch w
    | some (.ok _) => pure ⟨⟩

/-! ## The HTTP surface -/

def calendarApi : DbApi Calendar := api! [
  .get    "/hosts/{id:nat}/busy"         listBusy,
  .post   "/hosts/{id:nat}/availability" publish,
  .post   "/hosts/{id:nat}/bookings"     book,
  .get    "/bookings/{id:nat}"           readBooking,
  .delete "/bookings/{id:nat}"           cancelBooking
]

def stack (log : String → IO Unit := IO.eprintln) : Stack :=
  Stack.of [recover log, requestId, accessLog log, securityHeaders]

def service (dc : DbConns) (log : String → IO Unit := IO.eprintln) : Service :=
  calendarApi.service dc (stack log) log

end Scheduling
