import LeanDb.Model
import LeanApi.Core
import LeanApi.Native
open LeanDb.Model LeanApi.Core

/-! Generality fixture for an app with no accounts: public named counters, served by
`app% Name where api := api`. No person, credential, session or page; every operation takes
no actor. The current domain sits at the root namespace, as a small app's would; `CounterV1`
is the first deployment, before counters had a `step`, so the migration runs on a real old
database. `Reservations` stores a `represent`ed value. `scripts/ddd_counter_acceptance.mjs`
serves them over real curl and SQLite. -/

namespace CounterV1

structure Counter where
  name  : Name
  count : Nat
  deriving Entity

constraint Counter.uniqueName : unique name

inductive CreateError where
  | nameTaken

def newCounter (name : Name) : Op CreateError (Ref Counter) := do
  match ← Counter.insert { name, count := 0 } with
  | .ok id => pure id
  | .error .uniqueName => throw .nameTaken

def api : Api := [
  post "/counters" newCounter
]

end CounterV1

/-! ## The current counters (root namespace) -/

structure Counter where
  name  : Name
  count : Nat
  step  : Nat
  deriving Entity

-- One counter per name; a second `newCounter` is the typed `nameTaken`.
constraint Counter.uniqueName : unique name

inductive CreateError where
  | nameTaken

inductive CounterError where
  | notFound

structure CounterView where
  name  : Name
  count : Nat
  step  : Nat

def newCounter (name : Name) (step : Nat) : Op CreateError (Ref Counter) := do
  match ← Counter.insert { name, count := 0, step } with
  | .ok id => pure id
  | .error .uniqueName => throw .nameTaken

def increment (counter : Ref Counter) : Op CounterError Nat := do
  let some c ← Counter.find counter | throw .notFound
  let count := c.count + c.step
  -- The name is unchanged, so the update cannot conflict.
  let _ ← Counter.update c { c.toCounter with count }
  pure count

def getCounter (counter : Ref Counter) : ReadOp CounterError CounterView := do
  let some c ← Counter.find counter | throw .notFound
  return { name := c.name, count := c.count, step := c.step }

def api : Api := [
  post "/counters"                    newCounter,
  get  "/counters/:counter"           getCounter,
  post "/counters/:counter/increment" increment
]

/-! ## Reservations: a represented field

`Slot` has a private constructor, so every slot starts before it finishes. It is stored and sent
as its bounds (`represent … checked Slot.check`), and LeanDB keeps it as one column of that
codec's JSON, re-checked on every read. A stored slot that fails the check (a raw-SQL edit) is a
corruption fault: the request gets the framework error `storage.corrupt`, and the server keeps
serving. -/
namespace Reservations

structure Slot where
  private mk ::
  start  : Nat
  finish : Nat

def Slot.toPair (slot : Slot) : Nat × Nat := (slot.start, slot.finish)

def Slot.check : Nat × Nat → Except String Slot
  | (start, finish) => if start < finish then .ok ⟨start, finish⟩ else .error "start must precede finish"

represent Slot as Nat × Nat by Slot.toPair checked Slot.check

structure Reservation where
  room : Title
  slot : Slot
  deriving Entity

inductive ReservationError where
  | notFound

structure ReservationView where
  room : Title
  slot : Slot

def reserve (room : Title) (slot : Slot) : Op Empty (Ref Reservation) :=
  Reservation.insert { room, slot }

def getReservation (reservation : Ref Reservation) : ReadOp ReservationError ReservationView := do
  let some r ← Reservation.find reservation | throw .notFound
  return { room := r.room, slot := r.slot }

def cancel (reservation : Ref Reservation) : Op ReservationError Unit := do
  let some r ← Reservation.find reservation | throw .notFound
  Reservation.delete r

def api : Api := [
  post "/reservations"                     reserve,
  get  "/reservations/:reservation"        getReservation,
  post "/reservations/:reservation/cancel" cancel
]

end Reservations

app% reservations where
  api := Reservations.api

app% counterV1 where
  api := CounterV1.api

app% counters where
  api := api
  migrations := [
    -- Counters created before `step` existed counted by one.
    addStep := Counter.addField step (fill := 1)
  ]

def main (args : List String) : IO UInt32 := do
  let config : LeanApi.Native.AppConfig := { database := "counters.sqlite" }
  match args with
  | "v1" :: rest => counterV1.main rest config
  | "v2" :: rest => counters.main rest config
  -- The current build as it would be before its migration was written.
  | "v2-unmigrated" :: rest => LeanApi.Native.PublicApp.main { counters with migrations := [] } rest config
  | "reservations" :: rest => reservations.main rest { database := "reservations.sqlite" }
  | _ => do
    IO.eprintln "usage: leanapi_counter_app (v1 | v2 | v2-unmigrated | reservations) [migrate [--check]]"
    return 2
