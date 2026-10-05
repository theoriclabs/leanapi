import LeanDb.Model
import LeanApi.Core
import LeanApi.Native

/-! The native algebra on SQLite: an operation's embedded storage requests run through LeanDB's
native interpreter (typed rows, references and scopes, unique conflicts as values, foreign-key
faults as framework failures), the clock reads the request's sampled time, and every failed
command restores the whole state. `leanapi_native_checks read` and `… command`. -/
namespace NativeChecks
open LeanDb.Model LeanApi.Core

structure Profile where
  name : Name
  email : Email
  note : Text
  deriving Entity

structure Link where
  profile : Ref Profile
  label : Title
  deriving Entity

constraint Profile.uniqueName : unique name
constraint Profile.uniqueEmail : unique email

native_schema% S := Profile, Link
open LeanDb (IsSchema)

inductive AddError where
  | nameTaken
  | emailTaken
  | refused
  | missing

def add (name : Name) (email : Email) (note : Text) : Op AddError (Ref Profile) := do
  match ← Profile.insert { name, email, note } with
  | .ok id => pure id
  | .error .uniqueName => throw .nameTaken
  | .error .uniqueEmail => throw .emailTaken

def rename (id : Ref Profile) (name : Name) : Op AddError Unit := do
  let some p ← Profile.find id | throw .missing
  match ← Profile.update p { p.toProfile with name } with
  | .ok () => pure ()
  | .error .uniqueName => throw .nameTaken
  | .error .uniqueEmail => throw .emailTaken

def changeEmail (id : Ref Profile) (email : Email) : Op AddError Unit := do
  let some p ← Profile.find id | throw .missing
  match ← Profile.update p { p.toProfile with email } with
  | .ok () => pure ()
  | .error .uniqueName => throw .nameTaken
  | .error .uniqueEmail => throw .emailTaken

/-- A domain failure after a write: the write must not survive. -/
def lateAbort (name : Name) (email : Email) (note : Text) : Op AddError Unit := do
  let _ ← add name email note
  let ⟨_⟩ ← require False .refused
  pure ()

/-- A link to a profile that does not exist: a foreign-key fault, never a domain error. -/
def dangling (profile : Ref Profile) (label : Title) : Op AddError (Ref Link) :=
  Link.insert { profile, label }

derive_operation add
derive_operation rename
derive_operation changeEmail
derive_operation lateAbort
derive_operation dangling

open LeanDb (Txn DbM Read DbState Conn)

private def must (value : Except E A) : IO A := match value with
  | .ok value => pure value
  | .error _ => throw (IO.userError "native fixture setup failed")
private def check (value : Bool) (label : String) : IO Unit :=
  unless value do throw (IO.userError label)

abbrev R := LeanApi.Native.resources S

private def database (name : String) : IO LeanApi.DbConns := do
  let token ← LeanApi.Tokens.generate
  IO.FS.createDirAll ".lake/test-db"
  LeanApi.DbConns.open s!".lake/test-db/{name}-{token}.sqlite" (IsSchema.specs S) 1

private def execute (conn : LeanDb.Conn) (flow : {Scope : Type} → Flow .command Scope E A R) :
    IO (Contract.CallResult A E) := do
  must (← must (← DbM.run conn (Txn.runPrepared (pure ({now := 100} : LeanApi.Env)) (fun env => do
    match ← Flow.run (LeanApi.Native.commandAlgebra env) flow with
    | .ok value => return value
    | .error error => Txn.throw (.domain error)))))

private def sameTable {T} [LeanDb.Entity T] [LeanDb.IsSchema.Has S T] (a b : LeanDb.DbState S) : Bool :=
  let left := a.get (α := T)
  let right := b.get (α := T)
  left.next == right.next && left.rows.length == right.rows.length &&
    (left.rows.zip right.rows).all (fun (x,y) => x.id == y.id && LeanDb.Entity.encode x.val == LeanDb.Entity.encode y.val)

/-- One read request in a snapshot, at the native family. -/
private def readOnce (dc : LeanApi.DbConns) (now : Nat) (request : LeanApi.Core.Request Unit .query A R) :
    IO (Except (Contract.CallError Empty) A) := do
  must (← must (← DbM.run dc.writer.conn (Read.run (LeanApi.Native.readRequest (E := Empty) {now} request).run)))

def read : IO Unit := do
  let dc ← database "native-read"
  try
    let note ← must (Text.parse "persisted")
    let created ← execute dc.writer.conn (add.bodyWithResources (add.Requirements.infer (resources := R)) ()
      ⟨← must (Name.parse "Ada"), ← must (Email.parse "ada@example.com"), note⟩)
    let ada ← must created
    let storage := HasEntityResource.witness (family := R.toStorageResources) (T := Profile)
    let found ← readOnce dc 7 (.storage (.find storage ada))
    check (match found with | .ok (some row) => row.value.name.value == "Ada" && row.id == ada | _ => false)
      "witnessed find returns the stored record and its reference"
    let absent ← must (Ontology.Ref.parse (T := Profile) "999")
    check (match ← readOnce dc 7 (.storage (.find storage absent)) with | .ok none => true | _ => false) "a missing row"
    let wrongScope ← must (Ontology.Ref.parse (T := Profile) ada.key "other")
    check (match ← readOnce dc 7 (.storage (.find storage wrongScope)) with
      | .error (.protocol error) => error.code == "identity.invalid_reference" && error.status == some 400
      | _ => false) "another scope is a framework failure, never missing or domain"
    let rows ← readOnce dc 7 (.storage (.select storage))
    check (match rows with | .ok rows => rows.map (·.value.name.value) == ["Ada"] | _ => false) "select by identity"
    let byEmail ← readOnce dc 7 (.storage (.findBy storage Profile.uniqueEmail.key
      (HasUniqueResource.witness (family := R.toStorageResources) (storage := storage) (key := Profile.uniqueEmail.key))
      (← must (Email.parse "ADA@example.com"))))
    check (match byEmail with | .ok (some row) => row.id == ada | _ => false) "findBy through the declared unique's native index"
    let sampled ← readOnce dc 7 .now
    check (match sampled with | .ok now => now.value == 7 | _ => false) "the clock reads the sampled request time"
    check (match ← readOnce dc (2^63) .now with
      | .error (.protocol error) => error.code == "clock.invalid" && error.status == some 500
      | _ => false) "an invalid clock fails before producing an unchecked instant"
    IO.println "PASS native reads: find/select/findBy on SQLite, identity scope and clock framework failures"
  finally dc.close

def command : IO Unit := do
  let dc ← database "native-command"
  try
    let nameA ← must (Name.parse "A")
    let nameB ← must (Name.parse "B")
    let emailA ← must (Email.parse "a@example.com")
    let emailB ← must (Email.parse "b@example.com")
    let note ← must (Text.parse "persisted")
    let first ← must (← execute dc.writer.conn (add.bodyWithResources (add.Requirements.infer (resources := R)) () ⟨nameA, emailA, note⟩))
    discard <| must (← execute dc.writer.conn (add.bodyWithResources (add.Requirements.infer (resources := R)) () ⟨nameB, emailB, note⟩))
    let before ← must (← DbM.run dc.writer.conn (DbState.load (s := S)))
    let result ← execute dc.writer.conn (rename.bodyWithResources (rename.Requirements.infer (resources := R)) () ⟨first, nameB⟩)
    check (match result with | .error (.domain .nameTaken) => true | _ => false) "an update's touched unique: nameTaken"
    let result ← execute dc.writer.conn (changeEmail.bodyWithResources (changeEmail.Requirements.infer (resources := R)) () ⟨first, emailB⟩)
    check (match result with | .error (.domain .emailTaken) => true | _ => false) "an update's touched unique: emailTaken"
    let result ← execute dc.writer.conn (add.bodyWithResources (add.Requirements.infer (resources := R)) () ⟨nameA, emailB, note⟩)
    check (match result with | .error (.domain .nameTaken) | .error (.domain .emailTaken) => true | _ => false)
      "an insert reports an actual conflicting unique"
    let result ← execute dc.writer.conn (lateAbort.bodyWithResources (lateAbort.Requirements.infer (resources := R)) ()
      ⟨← must (Name.parse "Late"), ← must (Email.parse "late@example.com"), note⟩)
    check (match result with | .error (.domain .refused) => true | _ => false) "a domain failure after a write"
    let missing ← must (Ontology.Ref.parse (T := Profile) "999")
    let result ← execute dc.writer.conn (dangling.bodyWithResources (dangling.Requirements.infer (resources := R)) () ⟨missing, ← must (Title.parse "Link")⟩)
    check (match result with | .error (.protocol fault) => fault.code == "storage.missing_reference" && fault.status == some 409 | _ => false)
      "a dangling reference is a framework failure (409), never a domain error"
    let after ← must (← DbM.run dc.writer.conn (DbState.load (s := S)))
    check (sameTable (T := Profile) before after && sameTable (T := Link) before after && before.checkWF && after.checkWF)
      "every failed command restores rows and counters"
    let result ← execute (E := Empty) dc.writer.conn (.request (.hashPassword (← must (Password.parse "a long password"))))
    check (match result with | .error (.protocol fault) => fault.code == "auth.preparation_required" | _ => false)
      "a KDF request needs the preparation made before admission"
    IO.println "PASS native commands: conflicts as values, touched-field uniques, FK faults, late rollback, KDF preparation"
  finally dc.close

end NativeChecks
