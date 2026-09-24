/-
  Scheduling domain: values, decisions, proofs. No HTTP, no SQL.

  A host publishes aligned 30-minute slots. An invitee books one. Anyone
  may see the host's busy intervals; titles, notes and invitees are not
  part of that view. Proofs here are about the pure functions. Nothing
  in this file is stated over a database state.
-/
namespace Scheduling

/-! ## Bounds

Every numeric id and instant fits in a LeanDB `Ref` / SQLite INTEGER
(below 2^63). The bound lives on the type so storage never re-checks it. -/

/-- Unix seconds, UTC, below 2^63. -/
structure Instant where
  unix : Nat
  bound : unix < 2^63 := by decide
  deriving DecidableEq, Repr

def Instant.make (n : Nat) : Except String Instant :=
  if h : n < 2^63 then .ok ⟨n, h⟩ else .error "instant must be below 2^63"

def Instant.ofNat! (n : Nat) : Instant :=
  if h : n < 2^63 then ⟨n, h⟩ else ⟨0, by decide⟩

/-- A person (host or invitee). Zero is not a stored id. -/
structure PersonId where
  n : Nat
  lt : n < 2^63 := by decide
  deriving DecidableEq, Repr, Hashable, Ord

instance : Inhabited PersonId := ⟨⟨0, by decide⟩⟩

def PersonId.make (n : Nat) : Except String PersonId :=
  if h : n == 0 || n >= 2^63 then .error "person id must be between 1 and 2^63-1"
  else .ok ⟨n, by simp at h; omega⟩

def PersonId.ofNat! (n : Nat) : PersonId :=
  if h : n < 2^63 then ⟨n, h⟩ else ⟨0, by decide⟩

def PersonId.lit (n : Nat) (h : n < 2^63 := by decide) : PersonId := ⟨n, h⟩

theorem PersonId.ext {a b : PersonId} (h : a.n = b.n) : a = b := by
  cases a; cases b; simp_all

structure BookingId where
  n : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

def BookingId.make (n : Nat) : Except String BookingId :=
  if n == 0 || n >= 2^63 then .error "booking id must be between 1 and 2^63-1" else .ok ⟨n⟩

instance : ToString PersonId := ⟨fun p => toString p.n⟩
instance : ToString BookingId := ⟨fun b => toString b.n⟩

/-! ## Slots

Every bookable slot is 30 minutes, aligned to the Unix epoch. Distinct
aligned starts never overlap: that is `aligned_slots_disjoint`. -/

def slotSeconds : Nat := 1800

theorem slotSeconds_pos : 0 < slotSeconds := by decide

/-- An aligned 30-minute slot whose finish still fits in an `Instant`. -/
structure Slot where
  start : Instant
  aligned : start.unix % slotSeconds = 0
  fits : start.unix + slotSeconds < 2^63
  deriving DecidableEq, Repr

def Slot.make (t : Instant) : Except String Slot :=
  if h1 : t.unix % slotSeconds = 0 then
    if h2 : t.unix + slotSeconds < 2^63 then .ok ⟨t, h1, h2⟩
    else .error "slot would overflow 2^63"
  else .error "slot must be aligned to 30 minutes UTC"

def Slot.finish (s : Slot) : Instant := ⟨s.start.unix + slotSeconds, s.fits⟩

/-- Half-open `[start, finish)` in Unix seconds. -/
structure Interval where
  startUnix : Nat
  finishUnix : Nat
  deriving DecidableEq, Repr

def Slot.interval (s : Slot) : Interval := ⟨s.start.unix, s.finish.unix⟩

def Interval.overlaps (a b : Interval) : Bool :=
  a.startUnix < b.finishUnix && b.startUnix < a.finishUnix

/-! ## Text -/

structure Handle where
  raw : String
  deriving DecidableEq, Repr

def Handle.make (s : String) : Except String Handle :=
  let t := s.trimAscii.toString
  if t.isEmpty then .error "handle must be nonempty"
  else if t.length > 32 then .error "handle must be at most 32 characters"
  else .ok ⟨t⟩

structure Title where
  raw : String
  deriving DecidableEq, Repr

def Title.make (s : String) : Except String Title :=
  let t := s.trimAscii.toString
  if t.isEmpty then .error "title must be nonempty"
  else if t.length > 80 then .error "title must be at most 80 characters"
  else .ok ⟨t⟩

structure Notes where
  raw : String
  deriving DecidableEq, Repr

def Notes.make (s : String) : Except String Notes :=
  if s.length > 500 then .error "notes must be at most 500 characters" else .ok ⟨s⟩

def Notes.empty : Notes := ⟨""⟩

/-! ## Booking -/

structure Booking where
  id : BookingId
  host : PersonId
  invitee : PersonId
  slot : Slot
  title : Title
  notes : Notes
  deriving DecidableEq, Repr

def Booking.interval (b : Booking) : Interval := b.slot.interval

/-- What anyone may see: a busy interval, no title, notes or invitee. -/
structure BusyInterval where
  startUnix : Nat
  finishUnix : Nat
  deriving DecidableEq, Repr

def BusyInterval.ofSlot (s : Slot) : BusyInterval := ⟨s.start.unix, s.finish.unix⟩

def BusyInterval.ofInterval (i : Interval) : BusyInterval := ⟨i.startUnix, i.finishUnix⟩

def Booking.toBusy (b : Booking) : BusyInterval := BusyInterval.ofSlot b.slot

/-- Who may read a booking's details or cancel it. -/
def Booking.visibleTo (p : PersonId) (b : Booking) : Bool :=
  p == b.host || p == b.invitee

/-! ## Decisions -/

inductive BookRefuse where
  | inPast
  | notAvailable
  | taken
  deriving DecidableEq, Repr

/-- Sequential decision: in the future, inside published availability, and
    not already taken. Concurrent double-booking is the unique index, not
    this function. -/
def decideBook (now : Instant) (avail : List Slot) (taken : List Slot) (slot : Slot) :
    Except BookRefuse Unit :=
  if _h : now.unix ≥ slot.start.unix then .error .inPast
  else if _h : avail.contains slot = false then .error .notAvailable
  else if _h : taken.contains slot = true then .error .taken
  else .ok ()

inductive PublishRefuse where
  | inPast
  deriving DecidableEq, Repr

def decidePublish (now : Instant) (slot : Slot) : Except PublishRefuse Unit :=
  if _h : now.unix ≥ slot.start.unix then .error .inPast else .ok ()

/-- A calendar as a list of bookings. Pure. Used by the projection proofs. -/
def freeBusy (bs : List Booking) : List BusyInterval := bs.map Booking.toBusy

def retitle (b : Booking) (t : Title) : Booking := { b with title := t }

def renote (b : Booking) (n : Notes) : Booking := { b with notes := n }

def reinvite (b : Booking) (p : PersonId) : Booking := { b with invitee := p }

def occupied (bs : List Booking) (host : PersonId) (slot : Slot) : Bool :=
  bs.any fun b => b.host == host && b.slot == slot

def cancel (bs : List Booking) (id : BookingId) : List Booking :=
  bs.filter (·.id != id)

/-! ## Proofs

These are about the pure functions above. They are not theorems over
`DbState`: those would describe LeanDB's meaning, not yet the running
service (LeanDB M15). -/

theorem Instant.make_unix (t : Instant) : Instant.make t.unix = .ok t := by
  unfold Instant.make; simp [t.bound]

theorem Instant.ext {a b : Instant} (h : a.unix = b.unix) : a = b := by
  cases a; cases b; simp_all

theorem Slot.make_start (s : Slot) : Slot.make s.start = .ok s := by
  unfold Slot.make; simp [s.aligned, s.fits]

theorem Slot.finish_unix (s : Slot) : s.finish.unix = s.start.unix + slotSeconds := rfl

theorem Slot.interval_length (s : Slot) :
    s.interval.finishUnix = s.interval.startUnix + slotSeconds := rfl

private theorem aligned_eq_mul {n : Nat} (h : n % slotSeconds = 0) :
    n = slotSeconds * (n / slotSeconds) := by
  have := Nat.div_add_mod n slotSeconds
  rw [h, Nat.add_zero] at this
  exact this.symm

/-- Two aligned values, the smaller plus one slot, still ≤ the larger. -/
theorem next_aligned_le {n m : Nat}
    (hn : n % slotSeconds = 0) (hm : m % slotSeconds = 0) (hlt : n < m) :
    n + slotSeconds ≤ m := by
  have hn' := aligned_eq_mul hn
  have hm' := aligned_eq_mul hm
  have hlt' : slotSeconds * (n / slotSeconds) < slotSeconds * (m / slotSeconds) := by
    rwa [← hn', ← hm']
  have hq : n / slotSeconds < m / slotSeconds :=
    (Nat.mul_lt_mul_left slotSeconds_pos).mp hlt'
  have hle : n / slotSeconds + 1 ≤ m / slotSeconds := Nat.succ_le_of_lt hq
  have hmul : slotSeconds * (n / slotSeconds + 1) ≤ slotSeconds * (m / slotSeconds) :=
    Nat.mul_le_mul_left slotSeconds hle
  have : n + slotSeconds ≤ m := by
    rw [Nat.mul_add, Nat.mul_one, ← hn', ← hm'] at hmul
    exact hmul
  exact this

/-- Aligned, fixed-length slots with distinct starts never overlap. -/
theorem aligned_slots_disjoint (a b : Slot) (h : a.start ≠ b.start) :
    Interval.overlaps a.interval b.interval = false := by
  unfold Interval.overlaps Slot.interval Slot.finish
  have hne : a.start.unix ≠ b.start.unix := fun heq => h (Instant.ext heq)
  match Nat.lt_trichotomy a.start.unix b.start.unix with
  | .inl hlt =>
    have := next_aligned_le a.aligned b.aligned hlt
    simp [decide_eq_false_iff_not, Nat.not_lt]
    omega
  | .inr (.inl heq) => exact (hne heq).elim
  | .inr (.inr hgt) =>
    have := next_aligned_le b.aligned a.aligned hgt
    simp [decide_eq_false_iff_not, Nat.not_lt]
    omega

/-- Free/busy depends only on the intervals: same intervals, same busy list. -/
theorem freeBusy_congr {a b : List Booking}
    (h : a.map Booking.toBusy = b.map Booking.toBusy) :
    freeBusy a = freeBusy b := h

/-- Two calendars with the same slots but different titles give the same
    free/busy. Titles are not part of the declared release. -/
theorem retitle_preserves_freeBusy (bs : List Booking) (t : Title) :
    freeBusy (bs.map (retitle · t)) = freeBusy bs := by
  simp [freeBusy, retitle, Booking.toBusy, BusyInterval.ofSlot]

/-- Notes are not part of free/busy. -/
theorem renote_preserves_freeBusy (bs : List Booking) (n : Notes) :
    freeBusy (bs.map (renote · n)) = freeBusy bs := by
  simp [freeBusy, renote, Booking.toBusy, BusyInterval.ofSlot]

/-- Invitees are not part of free/busy. -/
theorem reinvite_preserves_freeBusy (bs : List Booking) (p : PersonId) :
    freeBusy (bs.map (reinvite · p)) = freeBusy bs := by
  simp [freeBusy, reinvite, Booking.toBusy, BusyInterval.ofSlot]

/-- The projection of one booking is exactly its interval. -/
theorem toBusy_eq_interval (b : Booking) :
    b.toBusy = ⟨b.interval.startUnix, b.interval.finishUnix⟩ := rfl

theorem toBusy_eq_ofInterval (b : Booking) :
    b.toBusy = BusyInterval.ofInterval b.interval := rfl

theorem decideBook_ok {now : Instant} {avail taken : List Slot} {slot : Slot}
    (h : decideBook now avail taken slot = .ok ()) :
    now.unix < slot.start.unix ∧ avail.contains slot = true ∧ taken.contains slot = false := by
  unfold decideBook at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · rename_i hPast hAvail hTaken
        refine ⟨Nat.not_le.mp hPast, ?_, ?_⟩
        · cases hcont : avail.contains slot
          · exact (hAvail hcont).elim
          · rfl
        · cases htk : taken.contains slot
          · rfl
          · exact (hTaken htk).elim

theorem decideBook_future {now : Instant} {avail taken : List Slot} {slot : Slot}
    (h : decideBook now avail taken slot = .ok ()) :
    now.unix < slot.start.unix := (decideBook_ok h).1

theorem decideBook_available {now : Instant} {avail taken : List Slot} {slot : Slot}
    (h : decideBook now avail taken slot = .ok ()) :
    avail.contains slot = true := (decideBook_ok h).2.1

theorem decidePublish_future {now : Instant} {slot : Slot}
    (h : decidePublish now slot = .ok ()) :
    now.unix < slot.start.unix := by
  unfold decidePublish at h
  split at h <;> simp_all

/-- Cancelling a booking frees its slot, provided no other booking of the
    same host occupies that slot (the unique-index invariant, as a list). -/
theorem cancel_frees (bs : List Booking) (b : Booking)
    (huniq : ∀ b' ∈ bs, b'.id = b.id ∨ b.host ≠ b'.host ∨ b.slot ≠ b'.slot) :
    occupied (cancel bs b.id) b.host b.slot = false := by
  simp only [occupied, cancel, List.any_eq_false, Bool.and_eq_true, beq_iff_eq]
  intro b' hb' ⟨hhost, hslot⟩
  have ⟨hmem, hid⟩ := List.mem_filter.mp hb'
  have hne : b'.id ≠ b.id := bne_iff_ne.mp hid
  rcases huniq b' hmem with h | h | h
  · exact hne h
  · exact h (hhost.symm)
  · exact h (hslot.symm)

/-- A host or invitee is visible to themselves. -/
theorem visibleTo_host (b : Booking) : Booking.visibleTo b.host b = true := by
  simp [Booking.visibleTo]

theorem visibleTo_invitee (b : Booking) : Booking.visibleTo b.invitee b = true := by
  simp [Booking.visibleTo]

end Scheduling
