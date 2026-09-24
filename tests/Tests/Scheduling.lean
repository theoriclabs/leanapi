/-
  Scheduling example: no double-booking, free/busy is a projection, and
  booking details stay with host and invitee. Compile-time refusals are
  pinned with `#guard_msgs`.
-/
import Scheduling.Api
import Scheduling.Bypass

namespace Tests.Schedule

open LeanApi LeanApi.Test Lean LeanDb Scheduling PolicyView

private def freshPath (name : String) : IO System.FilePath := do
  let dir : System.FilePath := ".lake/test-db"
  IO.FS.createDirAll dir
  let path := dir / s!"{name}.sqlite"
  for ext in ["", "-wal", "-shm"] do
    let f : System.FilePath := path.toString ++ ext
    if ← f.pathExists then IO.FS.removeFile f
  return path

private def bearer (t : String) : String × String := ("Authorization", s!"Bearer {t}")

private def must (r : Except DbError α) (what : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

private def jnat (r : Reply) (k : String) : Option Nat :=
  r.json?.bind fun j => (j.getObjValAs? Nat k).toOption

private def jstr (r : Reply) (k : String) : Option String :=
  r.json?.bind fun j => (j.getObjValAs? String k).toOption

/-- An aligned Unix instant well in the future (2033-05-18 00:10 UTC). -/
def future : Nat := 1999999800

/-- An aligned Unix instant in the past. -/
def past : Nat := 1000000800

def insertPerson (conn : Conn) (handle token : String) : IO Unit := do
  let h ← match Handle.make handle with
    | .ok h => pure h
    | .error e => throw (IO.userError e)
  let row := PersonRow.checked { handle := h, digest := Tokens.digest token }
  let r ← DbM.run conn (Txn.run (s := Calendar) (ε := Unit) fun {_σ} => do
    match ← Txn.insert PersonRow row with
    | .ok _ => pure ()
    | .error _ => Txn.throw ())
  match r with
  | .ok (.ok (.ok ())) => pure ()
  | _ => throw (IO.userError s!"insert person {handle}")

/-! ## Compile time -/

example : Handler.effect (σ := DbState Calendar) (τ := type_of% listBusy) = .reads := rfl
example : Handler.effect (σ := DbState Calendar) (τ := type_of% book) = .writes := rfl
example (u : Unique BookingRow) : u = BookingRow.Unique.bySlot := by cases u; rfl
example : Unique.Key (α := BookingRow) BookingRow.Unique.bySlot = (Ref PersonRow × Slot) := rfl

/--
error: could not synthesize default value for parameter 'safe' using tactics
---
error: a GET or HEAD endpoint must not change state, but this handler's effect is `writes`. Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.
-/
#guard_msgs (substring := true) in
example : DbEndpoint Calendar := .get "/hosts/{id:nat}/availability" publish

/-- error: Missing cases: -/
#guard_msgs (substring := true) in
example : InsertError BookingRow → String
  | .missingRef _ => "missing"

/-- error: Missing cases:
BookingRow.Unique.bySlot -/
#guard_msgs (substring := true) in
example : InsertError BookingRow → String
  | .missingRef _ => "missing"
  | .duplicate ix _ => nomatch ix

/-- The clash the unique index can produce: `bySlot`, handled. -/
example : InsertError BookingRow → String
  | .missingRef _ => "missing"
  | .duplicate .bySlot _ => "taken"

def run : TestM Unit := do
  section_ "scheduling: seed and free/busy projection" do
    let path ← freshPath "scheduling"
    let w ← must (← openDb path schema) "open"
    insertPerson w "alice" "alice-token"
    insertPerson w "bob" "bob-token"
    insertPerson w "cat" "cat-token"
    let dc ← DbConns.open path schema 2
    let svc := calendarApi.service dc {}
    let alice := "alice-token"
    let bob := "bob-token"
    let cat := "cat-token"
    let host := 1

    checkEq "busy empty 200" (← get svc s!"/hosts/{host}/busy").status 200
    checkEq "busy empty list"
      ((← get svc s!"/hosts/{host}/busy").json?.bind fun j =>
        (j.getObjVal? "busy").toOption.map fun | .arr xs => xs.size | _ => 99)
      (some 0)
    checkEq "no token on publish 401"
      (← postJson svc s!"/hosts/{host}/availability" (Json.mkObj [("start", Json.num future)])).status 401
    checkEq "bob cannot publish alice's slots"
      (← postJson svc s!"/hosts/{host}/availability" (Json.mkObj [("start", Json.num future)])
        [bearer bob]).status 404
    checkEq "unaligned start 422"
      (← postJson svc s!"/hosts/{host}/availability" (Json.mkObj [("start", Json.num (future + 1 : Nat))])
        [bearer alice]).status 422
    checkEq "past slot 422"
      (← postJson svc s!"/hosts/{host}/availability" (Json.mkObj [("start", Json.num past)])
        [bearer alice]).status 422
    let pub ← postJson svc s!"/hosts/{host}/availability" (Json.mkObj [("start", Json.num future)])
      [bearer alice]
    checkEq "alice publishes 201" pub.status 201
    checkEq "duplicate opening 409"
      (← postJson svc s!"/hosts/{host}/availability" (Json.mkObj [("start", Json.num future)])
        [bearer alice]).status 409

    let secret := "secret intro"
    let booked ← postJson svc s!"/hosts/{host}/bookings"
      (Json.mkObj [("start", Json.num future), ("title", .str secret), ("notes", .str "private notes")])
      [bearer bob]
    checkEq "bob books 201" booked.status 201
    checkEq "book location" (booked.header? "location") (some "/bookings/1")
    checkEq "title in details" (jstr booked "title") (some secret)
    let busy ← get svc s!"/hosts/{host}/busy"
    checkEq "busy after book 200" busy.status 200
    checkEq "one busy interval"
      (busy.json?.bind fun j => (j.getObjVal? "busy").toOption.map fun | .arr xs => xs.size | _ => 99)
      (some 1)
    check "free/busy does not contain the title" (!busy.body.contains secret)
    check "free/busy does not contain notes" (!busy.body.contains "private notes")
    check "free/busy does not contain invitee field" (!(busy.body.splitOn "invitee").length > 1)
    checkEq "busy start" (busy.json?.bind fun j =>
      match (j.getObjVal? "busy").toOption with
      | some (.arr xs) => xs[0]?.bind fun x => (x.getObjValAs? Nat "start").toOption
      | _ => none) (some future)

    checkEq "stranger cannot read details"
      (← get svc "/bookings/1" [bearer cat]).status 404
    checkEq "missing and hidden are the same 404"
      (← get svc "/bookings/999" [bearer bob]).status 404
    checkEq "bob reads details" (← get svc "/bookings/1" [bearer bob]).status 200
    checkEq "alice reads details" (jstr (← get svc "/bookings/1" [bearer alice]) "title") (some secret)
    checkEq "no token on details 401" (← get svc "/bookings/1").status 401

    checkEq "double book 409"
      (← postJson svc s!"/hosts/{host}/bookings"
        (Json.mkObj [("start", Json.num future), ("title", .str "second")])
        [bearer cat]).status 409

    checkEq "stranger cannot cancel" (← request svc "DELETE" "/bookings/1" [bearer cat]).status 404
    checkEq "bob cancels 204" (← request svc "DELETE" "/bookings/1" [bearer bob]).status 204
    checkEq "busy empty after cancel"
      ((← get svc s!"/hosts/{host}/busy").json?.bind fun j =>
        (j.getObjVal? "busy").toOption.map fun | .arr xs => xs.size | _ => 99)
      (some 0)
    let again ← postJson svc s!"/hosts/{host}/bookings"
      (Json.mkObj [("start", Json.num future), ("title", .str "rebooked")])
      [bearer cat]
    checkEq "cancel frees the slot" again.status 201
    dc.close

  section_ "scheduling: concurrent double-book" do
    let path ← freshPath "scheduling-conc"
    let w ← must (← openDb path schema) "open"
    insertPerson w "alice" "alice-token"
    insertPerson w "bob" "bob-token"
    insertPerson w "cat" "cat-token"
    let dc ← DbConns.open path schema 2
    let svc := calendarApi.service dc {}
    let _ ← postJson svc "/hosts/1/availability" (Json.mkObj [("start", Json.num future)])
      [bearer "alice-token"]
    let tasks ← (List.range 8).mapM fun i =>
      let tok := if i % 2 == 0 then "bob-token" else "cat-token"
      IO.asTask (postJson svc "/hosts/1/bookings"
        (Json.mkObj [("start", Json.num future), ("title", .str s!"t{i}")]) [bearer tok])
    let mut ok := 0
    let mut clash := 0
    for t in tasks do
      match ← IO.wait t with
      | .ok r => if r.status == 201 then ok := ok + 1 else if r.status == 409 then clash := clash + 1
      | .error _ => pure ()
    checkEq "exactly one concurrent booking wins" ok 1
    checkEq "the rest are 409 taken" clash 7
    checkEq "one busy interval after the race"
      ((← get svc "/hosts/1/busy").json?.bind fun j =>
        (j.getObjVal? "busy").toOption.map fun | .arr xs => xs.size | _ => 99)
      (some 1)
    dc.close

end Tests.Schedule
