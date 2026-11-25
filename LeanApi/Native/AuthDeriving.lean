import LeanApi.Native.AuthStorage
import LeanApi.Native.NativeResources
import LeanApi.Core.Auth
import LeanDb.Native

/-! Native session storage for an app with accounts. `app%` runs these with the app's own
names; they are ordinary commands, so the generated declarations can be `#print`ed. -/
namespace LeanApi.Native
open Lean Elab Command Meta

/-- The session table of an app with accounts: a library-owned private entity, never
published. `native_session_entity% Shop.Session for Shop.Customer`. -/
syntax "native_session_entity% " ident " for " ident : command
elab_rules : command
  | `(native_session_entity% $name:ident for $profile:ident) => do
    let rootIdent := LeanApi.Core.Declarations.rootIdent
    let profile ← resolveGlobalConstNoOverload profile
    let sessionName := name.getId.replacePrefix `_root_ .anonymous
    let sessId := rootIdent sessionName
    let profileId := rootIdent profile
    elabCommand (← `(structure $sessId where
      profile : Ontology.Ref $profileId
      digest : String
      csrfDigest : String
      expiresAt : Ontology.Instant
      revoked : Bool
      credentialVersion : Nat
      deriving LeanDb.Model.Entity))
    let byDigestId := rootIdent (sessionName ++ `byDigest)
    let digestPathId := rootIdent (sessionName ++ `digestPath)
    let uniqueName : Term := quote (sessionName.toString ++ ".byDigest")
    elabCommand (← `(def $byDigestId : LeanDb.Model.Unique $sessId String := ⟨$uniqueName, $digestPathId⟩))

/-- Native session storage for an app whose credential entity is authored, the one the domain
declared with `credential C.profileField C.hashField`:
`native_credential_storage% Shop.Db for Shop.Customer using Shop.Credential session Shop.Session`.
Sessions are checked on their own row (digest, expiry, revocation, live profile); the
credential table is written and read by the app's own operations. -/
syntax (name := nativeCredentialStorage) "native_credential_storage% " ident " for " ident " using " ident
  &"session" ident : command

@[command_elab nativeCredentialStorage]
def elabNativeCredentialStorage : CommandElab := fun stx => do
    let rootIdent := LeanApi.Core.Declarations.rootIdent
    let schema ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[1])
    let profile ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[3])
    let credential ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[5])
    let session ← resolveGlobalConstNoOverload (TSyntax.mk (ks := `ident) stx[7])
    -- The credential is the one the domain declared (`credential C.profileField C.hashField`).
    let link := credential ++ `credentialLink
    unless (← getEnv).contains link do
      throwError "{credential} is not a declared credential; declare `credential {credential}.<profile field> {credential}.<hash field>`"
    let s := rootIdent schema
    let p := rootIdent profile
    let t := rootIdent session
    let tUniqueByDigest := rootIdent (session ++ `Unique ++ `byDigest)
    let tProfile := rootIdent (session ++ `profile)
    let tExpires := rootIdent (session ++ `expiresAt)
    let tRevoked := rootIdent (session ++ `revoked)
    let tCsrf := rootIdent (session ++ `csrfDigest)
    let tVersion := rootIdent (session ++ `credentialVersion)
    let tMk := rootIdent (session ++ `mk)
    elabCommand (← `(@[reducible] instance : LeanApi.Native.Auth.HasStorage $s $p
        (LeanDb.Native.HasEntityStorage.storage (s := $s) (T := $p)) where
      storage := {
        Session := $t
        session := LeanDb.Native.HasEntityStorage.storage
        sessionMake := fun reference digest csrf expires version => $tMk reference digest csrf expires false version
        sessionProfile := $tProfile
        sessionExpires := $tExpires
        sessionRevoked := $tRevoked
        sessionCSRF := $tCsrf
        sessionVersion := $tVersion
        sessionLookup := fun digest => do
          return (← LeanDb.Read.lookup $t $tUniqueByDigest digest).map LeanDb.Valid.val
        revoke := fun digest => do
          let some row ← LeanDb.Txn.lookup $t $tUniqueByDigest digest | pure ()
          let reference ← LeanDb.Except.orAbort (LeanApi.Native.publicRef row.id) (fun _ => LeanApi.Native.fault "storage.invalid_identity")
          discard <| (LeanDb.Native.HasEntityStorage.storage (s := $s) (T := $t)).update (LeanDb.Model.Trusted.row (Scope := Unit) reference row.val)
            (LeanDb.Model.Change.set (field := "revoked") true) ([] : List (LeanDb.Model.Constraint Empty)) LeanApi.Native.storageFault }))
    -- Fix the concrete canonical dictionary at derivation time: instance search cannot recover
    -- this dependent dictionary from an unresolved family.
    elabCommand (← `(instance : LeanApi.Core.HasAuthResource (LeanApi.Native.resources $s) $p
      (LeanDb.Model.HasEntityResource.witness (family := (LeanApi.Native.resources $s).toStorageResources) (T := $p)) :=
      ⟨LeanApi.Native.Auth.HasStorage.storage⟩))

end LeanApi.Native
