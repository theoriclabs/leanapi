import LeanApiDomain.AuthStorage
import LeanApiDomain.NativeResources
import LeanDbDomain.Schema

namespace LeanApi.Domain
open Lean Elab Command Meta

private def generated (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .error error => throwError "native auth assembly: {error}\n{source}"
  | .ok command => elabCommand command

private def accountTypes (account : TSyntax `ident) : CommandElabM (Name × Name) := do
  let name ← resolveGlobalConstNoOverload account
  let type := (← getConstInfo name).type
  unless type.isAppOfArity ``LeanApp.Domain.Account 2 do
    throwErrorAt account "expected a portable Account declaration"
  let .const profile _ := type.getArg! 0
    | throwErrorAt account "native auth requires a declared profile type"
  return (name, profile)

/-- Generated private tables; application authors maintain neither rows nor
schemas. These entity representations are never Wire instances/publications. -/
syntax "native_auth_entities% " ident : command
elab_rules : command
  | `(native_auth_entities% $account:ident) => do
    let (name, profile) ← accountTypes account
    let base := "_root_." ++ name.toString ++ ".Native"
    let target := "_root_." ++ profile.toString
    generated ("@[entity] structure " ++ base ++ ".Credential where\n  profile : LeanApp.Domain.Ref " ++ target ++ "\n  passwordHash : String\n  version : Nat\n  enabled : Bool")
    generated ("def " ++ base ++ ".Credential.byProfile : LeanApp.Domain.Unique " ++ base ++ ".Credential (LeanApp.Domain.Ref " ++ target ++ ") := ⟨" ++ (Lean.Json.str (name.toString ++ ".Native.Credential.byProfile")).compress ++ ", " ++ base ++ ".Credential.profilePath⟩")
    generated ("@[entity] structure " ++ base ++ ".Session where\n  profile : LeanApp.Domain.Ref " ++ target ++ "\n  digest : String\n  csrfDigest : String\n  expiresAt : LeanApp.Domain.Instant\n  revoked : Bool\n  credentialVersion : Nat")
    generated ("def " ++ base ++ ".Session.byDigest : LeanApp.Domain.Unique " ++ base ++ ".Session String := ⟨" ++ (Lean.Json.str (name.toString ++ ".Native.Session.byDigest")).compress ++ ", " ++ base ++ ".Session.digestPath⟩")

syntax "native_auth_storage% " ident " for " ident : command
elab_rules : command
  | `(native_auth_storage% $schema:ident for $account:ident) => do
    let schema ← resolveGlobalConstNoOverload schema
    let (name, profile) ← accountTypes account
    let root := fun name : Name => "_root_." ++ name.toString
    let s := root schema
    let p := root profile
    let a := root name
    let c := a ++ ".Native.Credential"
    let t := a ++ ".Native.Session"
    let emailName ← liftTermElabM do
      let email ← whnf (← mkAppM ``LeanApp.Domain.Account.email #[mkConst name])
      let path ← whnf (← mkAppM ``Ontology.FieldPath.identity #[email])
      unless path.isAppOfArity ``List.cons 3 do throwError "auth email needs a direct field"
      let segment ← whnf (path.getArg! 1)
      let .lit (.strVal field) ← whnf (segment.getArg! 1)
        | throwError "auth email field is not a literal"
      pure field
    let uniques := LeanApp.Domain.uniqueDeclarations.getState (← getEnv)
    let emailUniques := (uniques.filter (fun entry => entry.owner == profile && entry.field == emailName)).map
      (·.identity.getString!)
    -- A named single-field constraint (`constraint Customer.uniqueEmail : unique email`) also counts.
    let constraints := LeanApp.Domain.Deriving.constraintDeclarations.getState (← getEnv)
    let emailConstraints := (constraints.filter (fun entry => entry.owner == profile &&
      entry.fields == #[Name.mkSimple emailName])).map (·.name.getString!)
    let emailKeys := (emailUniques ++ emailConstraints).toList.eraseDups
    unless emailKeys.length == 1 do throwError "native email auth requires exactly one declared email unique key"
    let unique := p ++ ".Unique." ++ emailKeys.head!
    generated ("@[reducible] instance : LeanApi.Domain.Auth.HasStorage " ++ s ++ " " ++ p ++ " (LeanDb.Domain.HasEntityStorage.storage (s := " ++ s ++ ") (T := " ++ p ++ ")) where\n" ++
      "  storage := {\n" ++
      "    Credential := " ++ c ++ "\n    credential := LeanDb.Domain.HasEntityStorage.storage\n" ++
      "    credentialMake := fun reference hash version => " ++ c ++ ".mk reference hash version true\n    credentialHash := " ++ c ++ ".passwordHash\n    credentialVersion := " ++ c ++ ".version\n    credentialEnabled := " ++ c ++ ".enabled\n" ++
      "    credentialLookup := fun reference => do\n      return (← LeanDb.Read.lookup " ++ c ++ " " ++ c ++ ".Unique.byProfile reference).map LeanDb.Valid.val\n" ++
      "    Session := " ++ t ++ "\n    session := LeanDb.Domain.HasEntityStorage.storage\n" ++
      "    sessionMake := fun reference digest csrf expires version => " ++ t ++ ".mk reference digest csrf expires false version\n" ++
      "    sessionProfile := " ++ t ++ ".profile\n    sessionExpires := " ++ t ++ ".expiresAt\n    sessionRevoked := " ++ t ++ ".revoked\n    sessionCSRF := " ++ t ++ ".csrfDigest\n    sessionVersion := " ++ t ++ ".credentialVersion\n" ++
      "    sessionLookup := fun digest => do\n      return (← LeanDb.Read.lookup " ++ t ++ " " ++ t ++ ".Unique.byDigest digest).map LeanDb.Valid.val\n" ++
      "    revoke := fun digest => do\n      let some row ← LeanDb.Txn.lookup " ++ t ++ " " ++ t ++ ".Unique.byDigest digest | pure ()\n      let reference ← LeanDb.Except.orAbort (LeanApi.Domain.publicRef row.id) (fun _ => LeanApi.Domain.Native.fault \"storage.invalid_identity\")\n      LeanApi.Domain.Native.change LeanDb.Domain.HasEntityStorage.storage (LeanApp.Domain.Trusted.row reference row.val) (LeanApp.Domain.Change.set (field := \"revoked\") true) []\n" ++
      "    profileLookup := fun address => do\n      let some row ← LeanDb.Read.lookup " ++ p ++ " " ++ unique ++ " address | return .ok none\n      match LeanApi.Domain.publicRef row.id with\n      | .error _ => return .error (LeanApi.Domain.Native.fault \"storage.invalid_identity\")\n      | .ok reference => return .ok (some (reference, row.val)) }")

    -- Fix the concrete canonical dictionary at derivation time. Generic instance
    -- search cannot recover this dependent dictionary from an unresolved family.
    generated ("instance : LeanApp.Domain.HasAuthResource (LeanApi.Domain.Native.resources " ++ s ++ ") " ++ p ++ " (LeanApp.Domain.HasEntityResource.witness (family := LeanApi.Domain.Native.resources " ++ s ++ ") (T := " ++ p ++ ")) := ⟨LeanApi.Domain.Auth.HasStorage.storage⟩")

/-- The session table of an app whose credential entity is authored (DDD-LAPI-06): a
library-owned private entity, never published. `native_session_entity% Shop.Session for Shop.Customer`. -/
syntax "native_session_entity% " ident " for " ident : command
elab_rules : command
  | `(native_session_entity% $name:ident for $profile:ident) => do
    let profile ← resolveGlobalConstNoOverload profile
    let sessionName := name.getId.replacePrefix `_root_ .anonymous
    let base := "_root_." ++ sessionName.toString
    generated ("@[entity] structure " ++ base ++ " where\n  profile : LeanApp.Domain.Ref _root_." ++ profile.toString ++
      "\n  digest : String\n  csrfDigest : String\n  expiresAt : LeanApp.Domain.Instant\n  revoked : Bool\n  credentialVersion : Nat")
    generated ("def " ++ base ++ ".byDigest : LeanApp.Domain.Unique " ++ base ++ " String := ⟨" ++
      (Lean.Json.str (sessionName.toString ++ ".byDigest")).compress ++ ", " ++ base ++ ".digestPath⟩")

/-- Native auth storage over an AUTHORED credential entity, the one the domain declared with
`credential C.profileField C.hashField`:
`native_credential_storage% Shop.Db for Shop.Customer using Shop.Credential session Shop.Session`.
Sessions are checked on their own row (digest, expiry, revocation, live profile). -/
syntax (name := nativeCredentialStorage) "native_credential_storage% " ident " for " ident " using " ident
  &"session" ident : command

@[command_elab nativeCredentialStorage]
def elabNativeCredentialStorage : CommandElab := fun stx => do
    let schema ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[1])
    let profile ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[3])
    let credential ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[5])
    let session ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[7])
    -- The credential is the one the domain declared (`credential C.profileField C.hashField`),
    -- read off `C.credentialLink`; nothing is inferred from the structure's shape.
    let link := credential ++ `credentialLink
    unless (← getEnv).contains link do
      throwError "{credential} is not a declared credential; declare `credential {credential}.<profile field> {credential}.<hash field>`"
    let fieldOf := fun (projection : Name) => liftTermElabM do
      let path ← whnf (← mkAppM ``Ontology.FieldPath.identity #[← mkAppM projection #[mkConst link]])
      unless path.isAppOfArity ``List.cons 3 do throwError "credential {credential}: the {projection} path is not a direct field"
      let segment ← whnf (path.getArg! 1)
      let .lit (.strVal field) ← whnf (segment.getArg! 1)
        | throwError "credential {credential}: the {projection} field is not a literal"
      pure (Name.mkSimple field)
    let refField ← fieldOf ``LeanApp.Domain.CredentialLink.profile
    let hashField ← fieldOf ``LeanApp.Domain.CredentialLink.hash
    let root := fun name : Name => "_root_." ++ name.toString
    let s := root schema
    let p := root profile
    let c := root credential
    let t := root session
    let r := refField.toString
    let h := hashField.toString
    generated ("@[reducible] instance : LeanApi.Domain.Auth.HasStorage " ++ s ++ " " ++ p ++ " (LeanDb.Domain.HasEntityStorage.storage (s := " ++ s ++ ") (T := " ++ p ++ ")) where\n" ++
      "  storage := {\n" ++
      "    Credential := " ++ c ++ "\n    credential := LeanDb.Domain.HasEntityStorage.storage\n" ++
      "    credentialMake := fun reference hash _ => { " ++ r ++ " := reference, " ++ h ++ " := LeanApp.Domain.Trusted.passwordHash hash }\n" ++
      "    credentialHash := fun value => LeanApp.Domain.Trusted.passwordHashText value." ++ h ++ "\n" ++
      "    credentialVersion := fun _ => 1\n    credentialEnabled := fun _ => true\n" ++
      "    credentialLookup := fun reference => do\n      match ← (LeanDb.Domain.HasEntityStorage.storage (s := " ++ s ++ ") (T := " ++ c ++ ")).select (Scope := Unit) with\n" ++
      "      | .ok rows => return (rows.find? (·.value." ++ r ++ " == reference)).map (·.value)\n      | .error _ => return none\n" ++
      "    Session := " ++ t ++ "\n    session := LeanDb.Domain.HasEntityStorage.storage\n" ++
      "    sessionMake := fun reference digest csrf expires version => " ++ t ++ ".mk reference digest csrf expires false version\n" ++
      "    sessionProfile := " ++ t ++ ".profile\n    sessionExpires := " ++ t ++ ".expiresAt\n    sessionRevoked := " ++ t ++ ".revoked\n    sessionCSRF := " ++ t ++ ".csrfDigest\n    sessionVersion := " ++ t ++ ".credentialVersion\n" ++
      "    sessionLookup := fun digest => do\n      return (← LeanDb.Read.lookup " ++ t ++ " " ++ t ++ ".Unique.byDigest digest).map LeanDb.Valid.val\n" ++
      "    revoke := fun digest => do\n      let some row ← LeanDb.Txn.lookup " ++ t ++ " " ++ t ++ ".Unique.byDigest digest | pure ()\n      let reference ← LeanDb.Except.orAbort (LeanApi.Domain.publicRef row.id) (fun _ => LeanApi.Domain.Native.fault \"storage.invalid_identity\")\n      LeanApi.Domain.Native.change LeanDb.Domain.HasEntityStorage.storage (LeanApp.Domain.Trusted.row reference row.val) (LeanApp.Domain.Change.set (field := \"revoked\") true) []\n" ++
      "    checksCredential := false }")
    generated ("instance : LeanApp.Domain.HasAuthResource (LeanApi.Domain.Native.resources " ++ s ++ ") " ++ p ++ " (LeanApp.Domain.HasEntityResource.witness (family := LeanApi.Domain.Native.resources " ++ s ++ ") (T := " ++ p ++ ")) := ⟨LeanApi.Domain.Auth.HasStorage.storage⟩")

end LeanApi.Domain
