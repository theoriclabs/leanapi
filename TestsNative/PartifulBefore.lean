import LeanDb.Model
import LeanApi.Core
import LeanApi.Native
open LeanDb.Model LeanApi.Core

/-! Partiful as first deployed, before `Party` gains `guestList` (the post's "Who can see
who's coming"). Same tables as `partiful_v2/` otherwise: `person`, `party`, `rsvp`,
`credential` and the app's `session`. `leanapi_apps partiful-before` serves it,
so `scripts/ddd_partiful_v2_acceptance.mjs` gets a real old database (real sign-ups, hashes,
parties and RSVPs) to hand to the milestone 2 binary: refused without the migration, then
backfilled by `partiful migrate`. -/
namespace PartifulBefore

structure Person where
  name  : Name
  email : Email
  deriving Entity

structure Party where
  host        : Ref Person
  title       : Title
  description : Text
  date        : Time
  deriving Entity

structure Rsvp where
  party : Ref Party
  guest : Ref Person
  deriving Entity

structure Credential where
  person : Ref Person
  hash   : PasswordHash
  deriving Entity

credential Credential.person Credential.hash
link Rsvp.party Rsvp.guest

constraint Person.uniqueEmail   : unique email
private constraint Rsvp.onePerGuest : unique (party, guest)
constraint Rsvp.cancelWithParty : cascade party

structure SignedIn where
  private mk ::
  id : Ref Person
  deriving Principal

inductive SignUpError where
  | emailTaken

def signUp (name : Name) (email : Email) (password : Password) :
    Op SignUpError Session := do
  match ← Person.insert { name, email } with
  | .error .uniqueEmail => throw .emailTaken
  | .ok id =>
    let _ ← Credential.insert { person := id, hash := ← password.hash }
    Auth.startSession id

inductive SignInError where
  | wrongEmailOrPassword

def signIn (email : Email) (password : Password) : Op SignInError Session := do
  let some id ← Credential.verify (← Person.findBy email) password
    | throw .wrongEmailOrPassword
  Auth.startSession id

def hostParty (me : SignedIn) (title : Title) (description : Text) (date : Time) :
    Op Empty (Ref Party) :=
  Party.insert { host := me.id, title, description, date }

inductive RsvpError where
  | notFound

def rsvp (me : SignedIn) (party : Ref Party) : Op RsvpError Unit := do
  let some p ← Party.find party | throw .notFound
  match ← Rsvp.insert { party := p.id, guest := me.id } with
  | .ok _               => pure ()
  | .error .onePerGuest => pure ()

structure Guest where
  name : Name

structure PartyPage where
  title       : Title
  description : Text
  date        : Time
  guests      : List Guest

inductive GetPartyError where
  | notFound

def getParty (party : Ref Party) : ReadOp GetPartyError PartyPage := do
  let some p ← Party.find party | throw .notFound
  let guests ← (·.map Guest.mk) <$> Query.linkField Rsvp.link.party.guest Person.namePath p.id
  return { title := p.title, description := p.description, date := p.date, guests }

def api : Api := [
  post "/sign-up"             signUp,
  post "/sign-in"             signIn,
  post "/parties"             hostParty,
  get  "/parties/:party"      getParty,
  post "/parties/:party/rsvp" rsvp
]

end PartifulBefore

app% PartifulBefore.server where
  authentication := PartifulBefore.Person with PartifulBefore.Credential
  api := PartifulBefore.api
