import LeanDb.Model
import LeanApi.Core
import LeanApi.Native

/-! The migration gate at app startup, with a real old database. `V1` is the app as first
deployed. `V2` is the same app after `Party` gains a required `guestList`, with the migration
listed in `app%`. `scripts/ddd_migration_acceptance.mjs` runs `leanapi_apps evolving`:
`v1` (serve, seed data), `v2-unmigrated` (the V2 build with no migration: must refuse and
exit non-zero), then `v2` (applies the backfill at startup and serves), plus the
`migrate --check` / `migrate` commands. -/
namespace Evolving
open LeanDb.Model LeanApi.Core

inductive GuestListVisibility where
  | everyone | attendees | hostOnly

inductive SignUpError where
  | emailTaken

inductive PartyError where
  | partyMissing

namespace V1

structure Person where
  name : Name
  email : Email
  deriving Entity

structure Login where
  person : Ref Person
  hash : PasswordHash
  deriving Entity

structure Party where
  host : Ref Person
  title : Title
  date : Time
  deriving Entity

credential Login.person Login.hash
constraint Person.byEmail : unique email

structure SignedIn where
  private mk ::
  id : Ref Person
  deriving Principal

def signUp (name : Name) (email : Email) (password : Password) : Op SignUpError Session := do
  match ← Person.insert { name, email } with
  | .error .byEmail => throw .emailTaken
  | .ok id =>
    let _ ← Login.insert { person := id, hash := ← password.hash }
    Auth.startSession id

def host (me : SignedIn) (title : Title) (date : Time) : Op Empty (Ref Party) :=
  Party.insert { host := me.id, title, date }

def partyTitle (viewer : Option SignedIn) (party : Ref Party) : ReadOp PartyError Title := do
  let some p ← Party.find party | throw .partyMissing
  return p.title

def api : Api := [
  post "/sign-up"         signUp,
  post "/parties"         host,
  get  "/parties/:party"  partyTitle
]
end V1

namespace V2

structure Person where
  name : Name
  email : Email
  deriving Entity

structure Login where
  person : Ref Person
  hash : PasswordHash
  deriving Entity

structure Party where
  host : Ref Person
  title : Title
  date : Time
  guestList : GuestListVisibility
  deriving Entity

credential Login.person Login.hash
constraint Person.byEmail : unique email

structure SignedIn where
  private mk ::
  id : Ref Person
  deriving Principal

def signUp (name : Name) (email : Email) (password : Password) : Op SignUpError Session := do
  match ← Person.insert { name, email } with
  | .error .byEmail => throw .emailTaken
  | .ok id =>
    let _ ← Login.insert { person := id, hash := ← password.hash }
    Auth.startSession id

def host (me : SignedIn) (title : Title) (date : Time) : Op Empty (Ref Party) :=
  Party.insert { host := me.id, title, date, guestList := .everyone }

def partyTitle (viewer : Option SignedIn) (party : Ref Party) : ReadOp PartyError Title := do
  let some p ← Party.find party | throw .partyMissing
  return p.title

def partyGuestList (viewer : Option SignedIn) (party : Ref Party) : ReadOp PartyError GuestListVisibility := do
  let some p ← Party.find party | throw .partyMissing
  return p.guestList

def api : Api := [
  post "/sign-up"                    signUp,
  post "/parties"                    host,
  get  "/parties/:party"             partyTitle,
  get  "/parties/:party/guest-list"  partyGuestList
]
end V2
end Evolving

app% Evolving.V1.app where
  authentication := Evolving.V1.Person with Evolving.V1.Login
  api := Evolving.V1.api

app% Evolving.V2.app where
  authentication := Evolving.V2.Person with Evolving.V2.Login
  api := Evolving.V2.api
  -- Existing parties behaved as `everyone`; the fill has the field's type.
  migrations := [
    addGuestList := Evolving.V2.Party.addField guestList (fill := .everyone)
  ]

/-- `evolving (v1 | v2 | v2-unmigrated) [migrate [--check]]`. -/
def Evolving.main (args : List String) : IO UInt32 := do
  let config : LeanApi.Native.AppConfig := { database := "evolving.sqlite" }
  match args with
  | "v1" :: rest => Evolving.V1.app.main rest config
  | "v2" :: rest => Evolving.V2.app.main rest config
  -- The V2 build as it would be with the migration not yet written.
  | "v2-unmigrated" :: rest => LeanApi.Native.NativeApp.main { Evolving.V2.app with migrations := [] } rest config
  | _ => do
    IO.eprintln "usage: leanapi_apps evolving (v1 | v2 | v2-unmigrated) [migrate [--check]]"
    return 2
