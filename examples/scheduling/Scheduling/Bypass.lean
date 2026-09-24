/-
  Compile-time refusals for the scheduling views. A separate module so
  `private mk` on `ProjRead` / `TxnAs` / `ReadAs` actually refuses.
-/
import Scheduling.Policies

open LeanDb PolicyView Scheduling

namespace Scheduling.Bypass

/-- error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.ReadAs` is marked as private -/
#guard_msgs (substring := true) in
/-- Bypass: an unscoped booking read, smuggled into the view. -/
def sneakyRead (me : Actor PersonId) (id : LeanDb.Id BookingRow) :
    ReadAs Calendar me (Option (Stored BookingRow)) :=
  ⟨Read.get BookingRow id⟩

/-- error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.Actor` is marked as private -/
#guard_msgs (substring := true) in
/-- Bypass: acting as another person. -/
def spoof (id : LeanDb.Id BookingRow) :
    ReadAs Calendar (⟨⟨2⟩⟩ : Actor PersonId) (Option (Stored BookingRow)) :=
  ReadAs.get BookingRow id

/-- error: Invalid `⟨...⟩` notation: Constructor for `Scheduling.ProjRead` is marked as private -/
#guard_msgs (substring := true) in
/-- Bypass: a full booking row, smuggled into the free/busy projection. -/
def sneakyBusy (host : PersonId) : ProjRead Calendar (Stored BookingRow) :=
  ⟨Read.all (BookingRow.busyOf host)⟩

/-- error: Invalid `⟨...⟩` notation: Constructor for `Scheduling.TxnAs` is marked as private -/
#guard_msgs (substring := true) in
/-- Bypass: an unscoped insert of a booking, smuggled into the write view. -/
def sneakyWrite {σ : Type} (p : PersonId) (r : Checked BookingRow) :
    TxnAs σ Calendar p Unit (Except (InsertError BookingRow) (Current σ BookingRow)) :=
  ⟨Txn.insert BookingRow r⟩

end Scheduling.Bypass
