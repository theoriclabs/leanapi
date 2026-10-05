import LeanApi
import LeanApp.Domain
import LeanApiDomain.NativeRead
import LeanDbDomain.Schema

namespace NativeReadChecks
open LeanDb LeanApp.Domain

@[entity] structure Item where
  label : String

@[entity] structure Group where
  label : String
  guests : Members Item := {}

native_schema% Database := Item, Group

query% itemLabel (viewer : Viewer Item) (id : LeanApp.Domain.Ref Item) : String := do
  let item ← find Item id else itemMissing
  return item.value.label

def requirements : itemLabel.Requirements (LeanApi.Domain.Native.resources Database) :=
  itemLabel.Requirements.infer

private def must (value : Except E A) : IO A :=
  match value with
  | .ok value => pure value
  | .error _ => throw (IO.userError "native read fixture setup failed")

private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

def run : IO Unit := do
  let token ← LeanApi.Tokens.generate
  IO.FS.createDirAll ".lake/test-db"
  let dc ← LeanApi.DbConns.open s!".lake/test-db/native-read-{token}.sqlite" (IsSchema.specs Database) 1
  try
    let item ← must (LeanDb.Entity.check Item ⟨"persisted"⟩)
    let group ← must (LeanDb.Entity.check Group ⟨"group", {}⟩)
    let seed : {Scope : Type} → Txn Scope Database String (LeanDb.Id Item × LeanDb.Id Group) := do
      let person ← Txn.insertNew item
      let parent ← Txn.insertNew group
      discard <| (← Txn.includeMember (Group.guestsRelation.bind parent) person.id).orAbort
        (fun _ => "fixture member insert failed")
      return (person.id, parent.id)
    let (itemId, groupId) ← must (← must (← must (← DbM.run dc.writer.conn (Txn.run seed))))
    let itemRef ← must (LeanApi.Domain.publicRef itemId)
    let groupRef ← must (LeanApi.Domain.publicRef groupId)
    let itemStorage := LeanApp.Domain.HasEntityResource.witness
      (family := LeanApi.Domain.Native.resources Database) (T := Item)
    let request : Request Unit Empty .query (Option (Row Unit Item)) (LeanApi.Domain.Native.resources Database) :=
      .find itemStorage itemRef
    let found ← must (← must (← must (← DbM.run dc.writer.conn
      (Read.run (LeanApi.Domain.Native.readRequest {now := 7} request).run))))
    check (found.any (fun row => row.value.label == "persisted" && row.id == itemRef))
      "witnessed read returns original nonempty record and nominal reference"
    let absent ← must (LeanApp.Domain.Ref.parse (T := Item) "999")
    let missing : Request Unit Empty .query (Option (Row Unit Item)) (LeanApi.Domain.Native.resources Database) :=
      .find itemStorage absent
    let found ← must (← must (← must (← DbM.run dc.writer.conn
      (Read.run (LeanApi.Domain.Native.readRequest {now := 7} missing).run))))
    check found.isNone "actual missing row"
    let wrongScope ← must (LeanApp.Domain.Ref.parse (T := Item) itemRef.key "other")
    let invalid : Request Unit Empty .query (Option (Row Unit Item)) (LeanApi.Domain.Native.resources Database) :=
      .find itemStorage wrongScope
    let result ← must (← must (← DbM.run dc.writer.conn
      (Read.run (LeanApi.Domain.Native.readRequest {now := 7} invalid).run)))
    check (match result with | .error (.protocol error) => error.code == "identity.invalid_reference" | _ => false)
      "unsupported scope remains framework failure, never missing or domain"
    let groupRow : Row Unit Group := LeanApp.Domain.Trusted.row groupRef group.val
    let handle := groupRow.membersField (resources := LeanApi.Domain.Native.resources Database) "guests"
    let present ← must (← must (← must (← DbM.run dc.writer.conn
      (Read.run (LeanApi.Domain.Native.contains (E := Empty) handle itemRef).run))))
    check present "typed existential edge executes nonempty indexed membership"
    let present ← must (← must (← must (← DbM.run dc.writer.conn
      (Read.run (LeanApi.Domain.Native.contains (E := Empty) handle absent).run))))
    check (!present) "absent member is false"
    let now : Request Unit Empty .query Instant (LeanApi.Domain.Native.resources Database) := .now
    let sampled ← must (← must (← must (← DbM.run dc.writer.conn
      (Read.run (LeanApi.Domain.Native.readRequest {now := 7} now).run))))
    check (sampled.value == 7) "shared checked Instant uses sampled environment"
    let overflow ← must (← must (← DbM.run dc.writer.conn
      (Read.run (LeanApi.Domain.Native.readRequest {now := 2^63} now).run)))
    check (match overflow with
      | .error (.protocol error) => error.code == "clock.invalid" && error.status == some 500
      | _ => false)
      "invalid native clock fails before producing unchecked scalar"
    IO.println "PASS: typed original-record lookup / native member witness / identity and clock framework failures"
  finally dc.close

end NativeReadChecks

def main : IO Unit := NativeReadChecks.run
