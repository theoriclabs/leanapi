import LeanApiDomain.Native
import LeanDbDomain.Schema

namespace NativeCommandsChecks
open LeanDb LeanApp.Domain

@[entity] structure Profile where
  name : Name
  email : Email
  note : Text
unique% Profile.byName := name
unique% Profile.byEmail := email

@[entity] structure Link where
  profile : LeanApp.Domain.Ref Profile
  label : Title

command% add (actor : Viewer Profile) (name : Name) (email : Email) (note : Text) : LeanApp.Domain.Ref Profile := do
  create Profile {name, email, note}

command% rename (actor : Viewer Profile) (id : LeanApp.Domain.Ref Profile) (name : Name) : Unit := do
  let row ← find Profile id else profileMissing
  change row {name}

command% changeEmail (actor : Viewer Profile) (id : LeanApp.Domain.Ref Profile) (email : Email) : Unit := do
  let row ← find Profile id else profileMissing
  change row {email}

command% lateAbort (actor : Viewer Profile) (name : Name) (email : Email) (note : Text) : Unit := do
  let _ ← create Profile {name, email, note}
  require false else refused

native_schema% S := Profile, Link

private def must (value : Except E A) : IO A := match value with
  | .ok value => pure value
  | .error _ => throw (IO.userError "native command fixture setup failed")
private def check (value : Bool) (label : String) : IO Unit :=
  unless value do throw (IO.userError label)

private def sameTable {T} [LeanDb.Entity T] [LeanDb.IsSchema.Has S T]
    (a b : LeanDb.DbState S) : Bool :=
  let left := a.get (α := T)
  let right := b.get (α := T)
  left.next == right.next && left.rows.length == right.rows.length &&
    (left.rows.zip right.rows).all (fun (x,y) => x.id == y.id && LeanDb.Entity.encode x.val == LeanDb.Entity.encode y.val)

private def execute (conn : LeanDb.Conn)
    (flow : {Scope : Type} → Flow .command Scope E A (LeanApi.Domain.Native.resources S)) :
    IO (Contract.CallResult A E) := do
  must (← must (← DbM.run conn (Txn.runPrepared (pure ({now := 100} : LeanApi.Env)) (fun env => do
    match ← Flow.run (LeanApi.Domain.Native.commandAlgebra env) flow with
    | .ok value => return value
    | .error error => Txn.throw (.domain error)))))

def run : IO Unit := do
  let token ← LeanApi.Tokens.generate
  IO.FS.createDirAll ".lake/test-db"
  let dc ← LeanApi.DbConns.open s!".lake/test-db/native-commands-{token}.sqlite" (IsSchema.specs S) 1
  try
    let nameA ← must (Name.parse "A")
    let nameB ← must (Name.parse "B")
    let emailA ← must (Email.parse "a@example.com")
    let emailB ← must (Email.parse "b@example.com")
    let note ← must (Text.parse "persisted")
    let first ← must (← execute dc.writer.conn (add.bodyWithResources add.Requirements.infer (Trusted.viewer none) ⟨nameA,emailA,note⟩))
    discard <| must (← execute dc.writer.conn (add.bodyWithResources add.Requirements.infer (Trusted.viewer none) ⟨nameB,emailB,note⟩))
    let before ← must (← DbM.run dc.writer.conn (DbState.load (s := S)))
    let result ← execute dc.writer.conn (rename.bodyWithResources rename.Requirements.infer (Trusted.viewer none) ⟨first,nameB⟩)
    check (match result with | .error (.domain .nameTaken) => true | _ => false) "exact touched name unique alternative"
    let result ← execute dc.writer.conn (changeEmail.bodyWithResources changeEmail.Requirements.infer (Trusted.viewer none) ⟨first,emailB⟩)
    check (match result with | .error (.domain .emailTaken) => true | _ => false) "exact touched email unique alternative"
    let result ← execute dc.writer.conn (add.bodyWithResources add.Requirements.infer (Trusted.viewer none) ⟨nameA,emailB,note⟩)
    check (match result with | .error (.domain .nameTaken) | .error (.domain .emailTaken) => true | _ => false) "create preserves actual conflicting unique alternative"
    let result ← execute dc.writer.conn (lateAbort.bodyWithResources lateAbort.Requirements.infer (Trusted.viewer none) ⟨← must (Name.parse "Late"),← must (Email.parse "late@example.com"),note⟩)
    check (match result with | .error (.domain .refused) => true | _ => false) "late generated flow domain failure"
    let after ← must (← DbM.run dc.writer.conn (DbState.load (s := S)))
    check (sameTable (T := Profile) before after && sameTable (T := Link) before after && before.checkWF && after.checkWF) "all failed commands restore rows and counters with WF"
    let missing ← must (LeanApp.Domain.Ref.parse (T := Profile) "999")
    let label ← must (Title.parse "Link")
    let result ← must (← must (← DbM.run dc.writer.conn (Txn.run (LeanApi.Domain.Native.create
      (LeanDb.Domain.HasEntityStorage.storage (s := S) (T := Link)) (Link.mk missing label)
      ([] : List (LeanApp.Domain.Constraint add.Error))))))
    check (match result with | .error (.protocol fault) => fault.code == "storage.unmapped_constraint" | _ => false)
      "unmapped typed native FK stays framework failure, never unrelated business unique"
    IO.println "PASS: native generic create/change/FK alternatives and populated late rollback"
  finally dc.close
end NativeCommandsChecks

def main : IO Unit := NativeCommandsChecks.run
