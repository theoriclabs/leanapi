import LeanApi.Core.Op

/-! # Authentication as ordinary operations (portable half of DDD-LAPI-06)

```
structure Login where
  member : Ref Member
  secret : PasswordHash
  deriving Entity
credential Login.member Login.secret        -- generates Login.credentialLink and Login.verify

structure SignedIn where
  private mk ::
  id : Ref Member
  deriving Principal

def register (name : Name) (email : Email) (password : Password) : Op RegisterError Session := do
  match ← Member.insert { name, email } with
  | .error .uniqueEmail => throw .alreadyRegistered
  | .ok id =>
    let _ ← Login.insert { member := id, secret := ← password.hash }
    Auth.startSession id

def logIn (email : Email) (password : Password) : Op LogInError Session := do
  let some id ← Login.verify (← Member.findBy email) password
    | throw .badCredentials
  Auth.startSession id
```

The credential entity is app code, opted in with `credential C.profileField C.hashField`. The
KDF steps are requests, so the runtime can hoist them before writer admission (decision 4):
publication records, in `FlowMetadata.kdf`, the input field each one consumes, and rejects an
operation whose KDF input is not one of its own arguments. -/

namespace LeanApi.Core
open Ontology LeanDb.Model

namespace Auth

/-- The credential check behind each generated `C.verify`. For `none` it still does the KDF
work (decision 2), so an unknown email and a wrong password cost the same. -/
def verifyWith [Entity C] [credentials : HasEntityResource portableStorage C] [Entity T] [HasRow T R]
    (link : CredentialLink C T) (profile : Option (R OpScope)) (password : Password) : Op ε (Option (Ref T)) :=
  Flow.request (.verifyCredential (resources := portableResources) credentials.witness link
    (profile.map (HasRow.toRow (T := T))) password)

/-- Start a session for `profile`, atomically with the operation's writes. The runtime sets the
cookie (or adds the token to a token-mode reply) only after commit. -/
def startSession [Entity T] [storage : HasEntityResource portableStorage T]
    [HasAuthResource portableResources T storage.witness] (profile : Ref T) : Op ε Session :=
  Flow.request (.startSession (resources := portableResources) storage.witness HasAuthResource.witness profile)

end Auth
end LeanApi.Core

/-- Hash a password with the runtime's KDF (`← password.hash` in an `Op`). Prepared before
writer admission. In namespace `Ontology.Password`, the type's own, so dot notation finds it. -/
def Ontology.Password.hash {ε : Type} (password : Ontology.Password) : LeanApi.Core.Op ε Ontology.PasswordHash :=
  LeanApi.Core.Flow.request (.hashPassword password)

namespace LeanApi.Core.Declarations
open Lean Elab Command Meta LeanDb.Model

private def full := LeanDb.Model.Deriving.full
private def quoted := LeanDb.Model.Deriving.quoted

/-- Field `field` of entity `owner`, with its (reducible-unfolded) type. -/
private def entityField (target : Syntax) : CommandElabM (Lean.Name × Lean.Name × Expr) := do
  let name := target.getId
  if name.getPrefix.isAnonymous then throwErrorAt target "expected Entity.field, e.g. `Login.member`"
  let owner ← liftCoreM <| realizeGlobalConstNoOverload (mkIdentFrom target name.getPrefix)
  unless (Deriving.entityDeclarations.getState (← getEnv)).any (·.name == owner) do
    throwErrorAt target "{owner} is not an entity; add `deriving Entity`"
  let field := Lean.Name.mkSimple name.getString!
  unless (getStructureFields (← getEnv) owner).contains field do
    throwErrorAt target "{owner} has no field `{field}`"
  let type ← liftTermElabM <| forallTelescopeReducing (← getConstInfo (owner ++ field)).type fun _ body => whnfR body
  return (owner, field, type)

/-- `credential C.profile C.hash`: entity `C` stores the password hash of the profile its
`profile : Ref P` field points to. Generates `C.credentialLink` and
`C.verify : Option (Row P) → Password → Op ε (Option (Ref P))`. -/
private def declareCredential (profileField hashField : Syntax) : CommandElabM Unit := do
  let (owner, profileName, profileType) ← entityField profileField
  let (owner', hash, hashType) ← entityField hashField
  unless owner == owner' do throwErrorAt hashField "both fields must belong to the same credential entity"
  unless hashType.isConstOf ``Ontology.PasswordHash do
    throwErrorAt hashField "`{hashField.getId}` must have type `PasswordHash`"
  unless profileType.isAppOfArity ``Ontology.EntityId 1 do
    throwErrorAt profileField "`{profileField.getId}` must have type `Ref T`"
  let .const profile _ := profileType.appArg! | throwErrorAt profileField "`{profileField.getId}` must reference an entity"
  unless (← getEnv).contains (profile ++ `Row) do throwErrorAt profileField "{profile} is not an entity with a row view"
  let ty := full owner
  let profileTy := full profile
  Deriving.runCommand ("def " ++ full (owner ++ `credentialLink) ++ " : LeanApi.Core.CredentialLink " ++ ty ++ " " ++ profileTy ++
    " := { identity := " ++ quoted owner.toString ++ ", profile := " ++ full (owner ++ .mkSimple (profileName.toString ++ "Path")) ++
    ", hash := " ++ full (owner ++ .mkSimple (hash.toString ++ "Path")) ++ " }")
  Deriving.runCommand ("def " ++ full (owner ++ `verify) ++ " {ε : Type} : Option (" ++ full (profile ++ `Row) ++
    " LeanDb.Model.OpScope) → Ontology.Password → LeanApi.Core.Op ε (Option (Ontology.Ref " ++ profileTy ++
    ")) := fun profile password => LeanApi.Core.Auth.verifyWith " ++ full (owner ++ `credentialLink) ++ " profile password")

/-- `credential C.profile C.hash` is one more reading of LeanDB's identifier-led
`E.a E.b` declaration shape (`link` is LeanDB's). -/
@[command_elab LeanDb.Model.Entities.entityFieldPair] def elabCredential : CommandElab := fun stx => do
  match stx[0].getId with
  | `credential => declareCredential stx[1] stx[2]
  | _ => throwUnsupportedSyntax

/-- `structure SignedIn where private mk :: id : Ref Customer deriving Principal`: the runtime
may fill this type from a verified session; nothing else can construct it. -/
initialize registerDerivingHandler ``LeanApi.Core.Principal fun names => do
  for name in names do
    let env ← getEnv
    unless isStructure env name do throwError "deriving Principal requires a structure with one `id : Ref Profile` field"
    let fields := getStructureFields env name
    unless fields.size == 1 do throwError "deriving Principal requires exactly one field `id : Ref Profile`; {name} has {fields.size}"
    let field := fields[0]!
    let profile ← liftTermElabM <| forallTelescopeReducing (← getConstInfo (name ++ field)).type fun _ body => do
      let body ← whnfR body
      unless body.isAppOfArity ``Ontology.EntityId 1 do
        throwError "deriving Principal: field {field} must have type `Ref Profile`"
      Deriving.sourceOf body.appArg!
    Deriving.runCommand ("instance : LeanApi.Core.Principal " ++ full name ++ " := { Profile := " ++ profile ++
      ", id := " ++ full (name ++ field) ++ ", trusted := fun id _ => ⟨id⟩ }")
  return true

end LeanApi.Core.Declarations
