import LeanApi.Native.AuthStorage
import LeanApi.Native.NativeResources
import LeanDb.Native

/-! Native session storage for an app with accounts. `app%` runs these with the app's own
names; they are ordinary commands, so the generated declarations can be `#print`ed. -/
namespace LeanApi.Native
open Lean Elab Command Meta

private def generated (source : String) : CommandElabM Unit := do
  match Parser.runParserCategory (← getEnv) `command source with
  | .error error => throwError "native auth assembly: {error}\n{source}"
  | .ok command => elabCommand command

/-- The session table of an app with accounts: a library-owned private entity, never
published. `native_session_entity% Shop.Session for Shop.Customer`. -/
syntax "native_session_entity% " ident " for " ident : command
elab_rules : command
  | `(native_session_entity% $name:ident for $profile:ident) => do
    let profile ← resolveGlobalConstNoOverload profile
    let sessionName := name.getId.replacePrefix `_root_ .anonymous
    let base := "_root_." ++ sessionName.toString
    generated ("structure " ++ base ++ " where\n  profile : Ontology.Ref _root_." ++ profile.toString ++
      "\n  digest : String\n  csrfDigest : String\n  expiresAt : Ontology.Instant\n  revoked : Bool\n  credentialVersion : Nat\n  deriving LeanDb.Model.Entity")
    generated ("def " ++ base ++ ".byDigest : LeanDb.Model.Unique " ++ base ++ " String := ⟨" ++
      (Lean.Json.str (sessionName.toString ++ ".byDigest")).compress ++ ", " ++ base ++ ".digestPath⟩")

/-- Native session storage for an app whose credential entity is authored, the one the domain
declared with `credential C.profileField C.hashField`:
`native_credential_storage% Shop.Db for Shop.Customer using Shop.Credential session Shop.Session`.
Sessions are checked on their own row (digest, expiry, revocation, live profile); the
credential table is written and read by the app's own operations. -/
syntax (name := nativeCredentialStorage) "native_credential_storage% " ident " for " ident " using " ident
  &"session" ident : command

@[command_elab nativeCredentialStorage]
def elabNativeCredentialStorage : CommandElab := fun stx => do
    let schema ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[1])
    let profile ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[3])
    let credential ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[5])
    let session ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[7])
    -- The credential is the one the domain declared (`credential C.profileField C.hashField`).
    let link := credential ++ `credentialLink
    unless (← getEnv).contains link do
      throwError "{credential} is not a declared credential; declare `credential {credential}.<profile field> {credential}.<hash field>`"
    let root := fun name : Name => "_root_." ++ name.toString
    let s := root schema
    let p := root profile
    let t := root session
    generated ("@[reducible] instance : LeanApi.Native.Auth.HasStorage " ++ s ++ " " ++ p ++ " (LeanDb.Native.HasEntityStorage.storage (s := " ++ s ++ ") (T := " ++ p ++ ")) where\n" ++
      "  storage := {\n" ++
      "    Session := " ++ t ++ "\n    session := LeanDb.Native.HasEntityStorage.storage\n" ++
      "    sessionMake := fun reference digest csrf expires version => " ++ t ++ ".mk reference digest csrf expires false version\n" ++
      "    sessionProfile := " ++ t ++ ".profile\n    sessionExpires := " ++ t ++ ".expiresAt\n    sessionRevoked := " ++ t ++ ".revoked\n    sessionCSRF := " ++ t ++ ".csrfDigest\n    sessionVersion := " ++ t ++ ".credentialVersion\n" ++
      "    sessionLookup := fun digest => do\n      return (← LeanDb.Read.lookup " ++ t ++ " " ++ t ++ ".Unique.byDigest digest).map LeanDb.Valid.val\n" ++
      "    revoke := fun digest => do\n      let some row ← LeanDb.Txn.lookup " ++ t ++ " " ++ t ++ ".Unique.byDigest digest | pure ()\n" ++
      "      let reference ← LeanDb.Except.orAbort (LeanApi.Native.publicRef row.id) (fun _ => LeanApi.Native.fault \"storage.invalid_identity\")\n" ++
      "      discard <| (LeanDb.Native.HasEntityStorage.storage (s := " ++ s ++ ") (T := " ++ t ++ ")).update (LeanDb.Model.Trusted.row (Scope := Unit) reference row.val)\n" ++
      "        (LeanDb.Model.Change.set (field := \"revoked\") true) ([] : List (LeanDb.Model.Constraint Empty)) LeanApi.Native.storageFault }")
    -- Fix the concrete canonical dictionary at derivation time: instance search cannot recover
    -- this dependent dictionary from an unresolved family.
    generated ("instance : LeanApi.Core.HasAuthResource (LeanApi.Native.resources " ++ s ++ ") " ++ p ++
      " (LeanDb.Model.HasEntityResource.witness (family := (LeanApi.Native.resources " ++ s ++ ").toStorageResources) (T := " ++ p ++
      ")) := ⟨LeanApi.Native.Auth.HasStorage.storage⟩")

end LeanApi.Native
