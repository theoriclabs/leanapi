/-
  LeanDB mapping for the scheduling example.

  Three tables. The unique index `BookingRow.bySlot` is the no-double-booking
  rule: a host's slot is stored at most once. `AvailabilityRow.bySlot` is
  the host's published openings. Policies (who may see which rows, and the
  free/busy projection) live in `Policies.lean`.

  Limits we stay inside (review D1–D10): no child lists, no enum order, no
  `Option (Ref _)`, no cascades, no `append`, every Nat below 2^63, every
  policy single-table (host and invitee sit on the booking row).
-/
import LeanDb
import Scheduling.Domain

namespace Scheduling

open LeanDb

/-! ## Column codecs from smart constructors -/

instance : ColCodec Instant := ColCodec.via (β := Nat) (·.unix) Instant.make
instance : ColCodec Slot := ColCodec.via (β := Instant) (·.start) Slot.make
instance : ColCodec Handle := ColCodec.via (β := String) (·.raw) Handle.make
instance : ColCodec Title := ColCodec.via (β := String) (·.raw) Title.make
instance : ColCodec Notes := ColCodec.via (β := String) (·.raw) Notes.make

/-- The `Nat` column codec round-trips below 2^63 (SQLite INTEGER range). -/
theorem nat_roundtrip (n : Nat) (h : n < 2^63) :
    (ColCodec.fromCol (ColCodec.toCol n) : Except String Nat) = .ok n := by
  have h1 : ¬ (Int64.ofNat n < 0) := by
    rw [Int64.lt_iff_toInt_lt]; simp [Int64.toInt_ofNat_of_lt h]
  have hmax : LeanDb.natSqlMax = 2^63 - 1 := by decide
  have hs : LeanDb.natToSql n = some (Int64.ofNat n) := by
    simp only [LeanDb.natToSql, hmax]; split <;> first | rfl | omega
  simp [ColCodec.fromCol, ColCodec.toCol, hs, h1, Int64.toNatClampNeg_ofNat_of_lt h]

theorem instant_roundtrip (t : Instant) :
    (ColCodec.fromCol (ColCodec.toCol t) : Except String Instant) = .ok t := by
  show (do Instant.make (← (ColCodec.fromCol (ColCodec.toCol t.unix) : Except String Nat))) = .ok t
  rw [nat_roundtrip t.unix t.bound]
  exact Instant.make_unix t

theorem slot_roundtrip (s : Slot) :
    (ColCodec.fromCol (ColCodec.toCol s) : Except String Slot) = .ok s := by
  show (do Slot.make (← (ColCodec.fromCol (ColCodec.toCol s.start) : Except String Instant))) = .ok s
  rw [instant_roundtrip]
  exact Slot.make_start s

/-! ## Entities -/

structure PersonRow where
  handle : Handle
  digest : String
  deriving Repr, LeanDb.Entity

structure AvailabilityRow where
  host : Ref PersonRow
  slot : Slot
  deriving Repr, LeanDb.Entity

structure BookingRow where
  host : Ref PersonRow
  invitee : Ref PersonRow
  slot : Slot
  title : Title
  notes : Notes
  deriving Repr, LeanDb.Entity

/-! ## Row ↔ domain -/

def pid (r : Ref PersonRow) : PersonId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩

def pref (p : PersonId) : Ref PersonRow := ⟨Int64.ofNat p.n⟩

def bidRef (b : BookingId) : LeanDb.Id BookingRow := ⟨Int64.ofNat b.n⟩

def BookingRow.toBooking (id : LeanDb.Id BookingRow) (r : BookingRow) : Booking :=
  { id := ⟨id.toInt64.toNatClampNeg⟩, host := pid r.host, invitee := pid r.invitee,
    slot := r.slot, title := r.title, notes := r.notes }

def BookingRow.ofBooking (b : Booking) : BookingRow :=
  { host := pref b.host, invitee := pref b.invitee, slot := b.slot,
    title := b.title, notes := b.notes }

def reconstruct (s : Stored BookingRow) : Booking := s.val.toBooking s.id

/-! ## Unique indexes and the schema

`BookingRow.bySlot` is the headline: inserting a second booking for the
same host and start is `InsertError.duplicate .bySlot`. That constructor
is the only inhabitant of `Unique BookingRow`; adding another unique
index makes every `nomatch` on it stop compiling. -/

unique% PersonRow.byHandle := handle
unique% PersonRow.byDigest := digest
unique% AvailabilityRow.bySlot := (host, slot)
unique% BookingRow.bySlot := (host, slot)

schema% Calendar := PersonRow, AvailabilityRow, BookingRow

def schema : List TableSpec := IsSchema.specs Calendar

/-! ## `Checked` rows

No row invariant beyond the types: a `Slot` is aligned, titles and notes
are already constructed. `Invariant` is `True`, so `Checked.of _ trivial`
needs no runtime check. -/

def PersonRow.checked (r : PersonRow) : Checked PersonRow := Checked.of r trivial

def AvailabilityRow.checked (r : AvailabilityRow) : Checked AvailabilityRow :=
  Checked.of r trivial

def BookingRow.checked (r : BookingRow) : Checked BookingRow := Checked.of r trivial

theorem pid_lt (r : Ref PersonRow) : (pid r).n < 2^63 := (pid r).lt

theorem pid_pref (p : PersonId) : pid (pref p) = p := by
  cases p with
  | mk n h => simp [pid, pref, Int64.toNatClampNeg_ofNat_of_lt h]

theorem BookingRow.toBooking_ofBooking (b : Booking) (hid : b.id.n < 2^63)
    (hh : b.host.n < 2^63 := b.host.lt) (hi : b.invitee.n < 2^63 := b.invitee.lt) :
    (BookingRow.ofBooking b).toBooking ⟨Int64.ofNat b.id.n⟩ = b := by
  have hx := pid_pref b.host
  have hy := pid_pref b.invitee
  cases b
  simp_all [BookingRow.toBooking, BookingRow.ofBooking, Int64.toNatClampNeg_ofNat_of_lt hid]

end Scheduling
