import LeanApiDomain.App
import LeanDb.Typed.Gate
import PartifulBefore

/-! The migration gate at app startup, with a real old database. `V1` is the app as first
deployed. `V2` is the same app after `Party` gains a required `guestList`, with the
migration listed in `app%`. `scripts/ddd_migration_acceptance.mjs` runs this binary:
`v1` (serve, seed data), `v2-unmigrated` (the V2 build with no migration: must refuse and
exit non-zero), then `v2` (applies the backfill at startup and serves), plus the
`migrate --check` / `migrate` commands. -/
namespace Evolving
open LeanApp.Domain

inductive GuestListVisibility where
  | everyone | attendees | hostOnly
  deriving Domain

namespace V1
@[entity] structure Person where
  name : Name
  email : Email

unique% Person.byEmail := email

@[entity] structure Party where
  host : Ref Person
  title : Title
  date : Instant

auth% account : Person using emailPassword(email)

command% host (me : SignedIn Person) (title : Title) (date : Instant) : Ref Party := do
  create Party { host := me.id, title, date }

query% partyTitle (viewer : Viewer Person) (party : Ref Party) : Title := do
  let p ← find Party party else partyMissing
  return p.value.title
end V1

namespace V2
@[entity] structure Person where
  name : Name
  email : Email

unique% Person.byEmail := email

@[entity] structure Party where
  host : Ref Person
  title : Title
  date : Instant
  guestList : GuestListVisibility

auth% account : Person using emailPassword(email)

command% host (me : SignedIn Person) (title : Title) (date : Instant) : Ref Party := do
  create Party { host := me.id, title, date, guestList := .everyone }

query% partyTitle (viewer : Viewer Person) (party : Ref Party) : Title := do
  let p ← find Party party else partyMissing
  return p.value.title

query% partyGuestList (viewer : Viewer Person) (party : Ref Party) : GuestListVisibility := do
  let p ← find Party party else partyMissing
  return p.value.guestList
end V2
end Evolving

app% Evolving.V1.app where
  authentication := Evolving.V1.account
  routes := [
    post "/sign-up" Evolving.V1.account.signUp,
    post "/parties" Evolving.V1.host,
    get "/parties/:party" Evolving.V1.partyTitle
  ]
  pages := []

app% Evolving.V2.app where
  authentication := Evolving.V2.account
  routes := [
    post "/sign-up" Evolving.V2.account.signUp,
    post "/parties" Evolving.V2.host,
    get "/parties/:party" Evolving.V2.partyTitle,
    get "/parties/:party/guest-list" Evolving.V2.partyGuestList
  ]
  pages := []
  -- Existing parties behaved as `everyone`; the fill has the field's type.
  migrations := [
    addGuestList := Evolving.V2.Party.addField guestList (fill := .everyone)
  ]

def main (args : List String) : IO UInt32 := do
  let config : LeanApi.Domain.AppConfig := { database := "evolving.sqlite" }
  match args with
  | "v1" :: rest => Evolving.V1.app.main rest config
  | "v2" :: rest => Evolving.V2.app.main rest config
  -- The V2 build as it would be with the migration not yet written.
  | "v2-unmigrated" :: rest => LeanApi.Domain.NativeApp.main { Evolving.V2.app with migrations := [] } rest config
  -- Partiful before `guestList` (PartifulBefore.lean): the milestone 2 app's old database.
  | "partiful-before" :: rest => PartifulBefore.server.main rest { config with database := "partiful.sqlite" }
  | _ => do
    IO.eprintln "usage: domain_migration_checks (v1 | v2 | v2-unmigrated | partiful-before) [migrate [--check]]"
    return 2
