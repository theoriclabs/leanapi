/-
  Notes, written with typed endpoints (docs/ENDPOINTS.md).

  Each endpoint is a pure function; its signature says what it takes, from
  where, whether it changes state, and every way it can answer. The route
  table at the bottom is the whole HTTP surface.

  Auth: bearer token, or the `sid` cookie; login uses Basic credentials.
  Passwords are compared directly here to keep the example small;
  `examples/private-games` uses the crypto dependency. State: in memory.
-/
import LeanApi

namespace Notes

open LeanApi Lean

/-! ## Domain values: validated at the boundary -/

structure Title where
  raw : String
  deriving Repr, BEq

instance : SmartCtor Title String where
  make s :=
    let t := s.trimAscii.toString
    if t.isEmpty then .error "title must be nonempty"
    else if t.length > 200 then .error "title must be at most 200 characters"
    else .ok ⟨t⟩
  raw := (·.raw)

structure UserName where
  raw : String
  deriving Repr, BEq

instance : SmartCtor UserName String where
  make s := if s.isEmpty then .error "name required" else .ok ⟨s⟩
  raw := (·.raw)

structure Password where
  raw : String

instance : SmartCtor Password String where
  make s := if s.length < 4 then .error "password must be at least 4 characters" else .ok ⟨s⟩
  raw := (·.raw)

structure NoteId where
  n : Nat
  deriving BEq

instance : FromParam NoteId := ⟨fun s => (FromParam.fromParam s).map NoteId.mk⟩

/-- A note's revision, as sent back in `If-Match`. -/
structure Rev where
  n : Nat
  deriving BEq

instance : FromParam Rev := ⟨fun s => (FromParam.fromParam s).map Rev.mk⟩

/-! ## State -/

structure Note where
  id : Nat
  owner : String
  title : Title
  body : String
  rev : Nat := 1

structure State where
  users : List (String × String) := []
  tokens : List (String × String) := []
  notes : Array Note := #[]
  nextId : Nat := 1

abbrev Db := Std.Mutex State

def Db.new : IO Db := Std.Mutex.new {}

def read (db : Db) (f : State → α) : IO α := db.atomically do return f (← get)

def ownNote (s : State) (who : String) (id : Nat) : Option Note :=
  s.notes.find? fun n => n.id == id && n.owner == who

/-! ## Actors: one type per authentication scheme -/

/-- Authenticated by a session token (bearer or the `sid` cookie). -/
structure User where
  name : String

/-- Authenticated by Basic credentials. -/
structure ByPassword where
  name : String

instance : Authenticates State User :=
  .sessions (fun s t => (s.tokens.lookup t).map (⟨·⟩)) (cookie := some "sid")

instance : Authenticates State ByPassword :=
  .passwords fun s u p => if s.users.lookup u == some p then some ⟨u⟩ else none

/-! ## Requests -/

structure Register where
  name : UserName
  password : Password

instance : FromBody Register := .record (Register.mk <$> .req "name" <*> .req "password")
instance : FromForm Register := .record (Register.mk <$> .req "name" <*> .req "password")

structure NewNote where
  title : Title
  body : String

instance : FromBody NewNote := .record (NewNote.mk <$> .req "title" <*> .dflt "body" "")

structure NoteEdit where
  title : Option Title
  body : Option String

instance : FromBody NoteEdit := .record (NoteEdit.mk <$> .opt "title" <*> .opt "body")

/-- A page request: `page ≥ 1`, `1 ≤ per ≤ 100`, checked on decoding. -/
structure Page where
  page : Nat
  per : Nat

instance : FromQuery Page where
  fromQuery r := do
    let (page, per) ← ((·, ·) <$> Extract.queryD "page" 1 <*> Extract.queryD "per" 20) r
    if page == 0 || per == 0 || per > 100 then .error [⟨"query.per", "page ≥ 1, 1 ≤ per ≤ 100"⟩]
    else .ok ⟨page, per⟩

/-! ## Responses and failures -/

structure UserView where
  name : String
  deriving ToJson

structure Session where
  token : String
  deriving ToJson

structure NoteView where
  id : Nat
  title : String
  body : String
  rev : Nat
  deriving ToJson

def Note.view (n : Note) : NoteView := ⟨n.id, n.title.raw, n.body, n.rev⟩

def Note.versioned (n : Note) : Versioned NoteView := ⟨n.view, n.rev⟩

inductive RegisterError | nameTaken

instance : ToProblem RegisterError where
  status | .nameTaken => ⟨409, by decide⟩
  detail | .nameTaken => some "name taken"

inductive EditError | notFound | stale

instance : ToProblem EditError where
  status | .notFound => ⟨404, by decide⟩ | .stale => ⟨412, by decide⟩
  detail | .notFound => none | .stale => some "note changed"

/-! ## Endpoints -/

/-- Register a new user (JSON or form). -/
def register (u : Body Register) : Writes State (Except RegisterError (Created UserView)) := fun s =>
  let name := u.val.name.raw
  if (s.users.lookup name).isSome then (s, .error .nameTaken)
  else ({ s with users := (name, u.val.password.raw) :: s.users }, .ok { val := ⟨name⟩ })

/-- Log in with Basic credentials; the new session token is also set as the
    `sid` cookie. -/
def login (who : Auth ByPassword) (tok : FreshToken) : Writes State (Created (WithCookie Session)) := fun s =>
  ({ s with tokens := (tok.val, who.val.name) :: s.tokens },
   { val := ⟨⟨tok.val⟩, { name := "sid", value := tok.val }⟩ })

/-- One page of my notes. -/
def listNotes (me : Auth User) (p : Query Page) : Reads State (Paged NoteView) := fun s =>
  let mine := s.notes.filter (·.owner == me.val.name)
  ⟨((mine.toList.drop ((p.val.page - 1) * p.val.per)).take p.val.per).map Note.view, mine.size, p.val.page⟩

/-- Create a note. -/
def createNote (me : Auth User) (new : Body NewNote) : Writes State (Created (Versioned NoteView)) := fun s =>
  let n : Note := { id := s.nextId, owner := me.val.name, title := new.val.title, body := new.val.body }
  ({ s with notes := s.notes.push n, nextId := s.nextId + 1 },
   { val := n.versioned, location := some s!"/api/notes/{n.id}" })

/-- One of my notes. Someone else's note is indistinguishable from a missing one. -/
def getNote (me : Auth User) (id : Path NoteId) : Reads State (Except NotFound (Versioned NoteView)) := fun s =>
  match ownNote s me.val.name id.val.n with
  | some n => .ok n.versioned
  | none => .error {}

/-- Edit one of my notes, if it hasn't changed since `rev`. -/
def editNote (me : Auth User) (id : Path NoteId) (rev : IfMatch Rev) (edit : Body NoteEdit) :
    Writes State (Except EditError (Versioned NoteView)) := fun s =>
  match ownNote s me.val.name id.val.n with
  | none => (s, .error .notFound)
  | some n =>
    if rev.val.any (·.n != n.rev) then (s, .error .stale) else
    let n' := { n with title := edit.val.title.getD n.title, body := edit.val.body.getD n.body, rev := n.rev + 1 }
    ({ s with notes := s.notes.map fun x => if x.id == n.id then n' else x }, .ok n'.versioned)

/-- Delete one of my notes. -/
def deleteNote (me : Auth User) (id : Path NoteId) : Writes State (Except NotFound NoContent) := fun s =>
  match ownNote s me.val.name id.val.n with
  | none => (s, .error {})
  | some n => ({ s with notes := s.notes.filter (·.id != n.id) }, .ok {})

/-! ## The HTTP surface -/

def api : Api State := api! [
  .post   "/users"             register,
  .post   "/sessions"          login,
  .get    "/notes"             listNotes,
  .post   "/notes"             createNote,
  .get    "/notes/{id:nat}"    getNote,
  .patch  "/notes/{id:nat}"    editNote (limit := 64 * 1024),
  .delete "/notes/{id:nat}"    deleteNote
]

def stack (log : String → IO Unit := IO.eprintln) : Stack := Stack.of [
  recover log, requestId, accessLog log, health, securityHeaders,
  cors { origins := .list ["http://localhost:5173"], credentials := true },
  trustedProxy ["127.0.0.1"], timeout 10000]

def service (db : Db) (log : String → IO Unit := IO.eprintln) : Service :=
  (api.under "/api").service (.ofMutex db) (stack log)

end Notes
