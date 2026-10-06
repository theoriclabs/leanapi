import LeanApi.Native.Auth
import LeanApi.Native.NativeStorage

namespace LeanApi.Native.Auth
open LeanApi LeanDb LeanDb.Model LeanApi.Core Ontology

/-- The session storage of an app with accounts, generated with the schema
(`native_credential_storage%`). Credentials and sessions are private storage, never
contracts or an extra authentication API: the credential table is the app's own entity
(`credential C.profile C.hash`), written by its own operations. -/
structure Storage (s Profile : Type) [IsSchema s]
    (profile : LeanDb.Native.EntityStorage s Profile) : Type 1 where
  Session : Type
  session : LeanDb.Native.EntityStorage s Session
  sessionMake : Ontology.Ref Profile → String → String → Instant → Nat → Session
  sessionProfile : Session → Ontology.Ref Profile
  sessionExpires : Session → Instant
  sessionRevoked : Session → Bool
  sessionCSRF : Session → String
  sessionVersion : Session → Nat
  sessionLookup : String → Read s (Option Session)
  revoke : {Scope E : Type} → String → Native.CommandM Scope s E Unit

class HasStorage (s Profile : Type) [schema : outParam (IsSchema s)]
    (profile : outParam (LeanDb.Native.EntityStorage s Profile)) : Type 1 where
  storage : Storage s Profile profile

private def insertPrivate {s Scope T E} [IsSchema s]
    (storage : LeanDb.Native.EntityStorage s T) (value : T) : Native.CommandM Scope s E Unit :=
  letI := storage.entity
  letI := storage.unique
  letI := storage.foreignKey
  letI := storage.schema
  do
    let checked ← (LeanDb.Entity.check T value).orAbort
      (fun _ => Native.fault "auth.invalid_storage")
    discard <| (Txn.insert T checked).orAbort fun
      | .duplicate _ _ => Native.fault "auth.storage_duplicate"
      | .missingRef _ => Native.fault "auth.storage_missing_reference"

/-- The live session with this token digest: its row, expiry, revocation, CSRF digest and the
live profile it names. -/
def Storage.live {s Profile Scope} [IsSchema s] [LeanDb.Model.Entity Profile]
    {profile : LeanDb.Native.EntityStorage s Profile} (store : Storage s Profile profile)
    (digest : String) : Read s (Option (LiveSession Scope Profile)) := do
  let some session ← store.sessionLookup digest | return none
  let reference := store.sessionProfile session
  match profile.find reference with
  | .error _ => return none
  | .ok program =>
    let live ← program
    return some { profile := live
                  expiresAt := store.sessionExpires session
                  enabled := true
                  revoked := store.sessionRevoked session
                  csrfDigest := store.sessionCSRF session }

/-! ## Authored authentication (DDD-LAPI-06, design D)

The KDF steps an operation reaches (`FlowMetadata.kdf`) are prepared before writer admission,
under `KDFGate`; the admitted flow's `hashPassword`/`verifyCredential` requests are answered
from this preparation, and `startSession` inserts the session row prepared here. -/

/-- One prepared `verifyCredential`: the profile it looked up (or none), the stored hash it
verified against (or the dummy), and the verdict. -/
structure Verified where
  private mk ::
  profile : Option String
  private password : String
  stored : Option String
  accepted : Bool

/-- Native preparation of an authored operation. No `Repr`/`Wire`: it holds a raw token. -/
structure Preparation where
  private mk ::
  private hashes : List (String × String)
  verifications : List Verified
  session : Prepared

def Preparation.create (hashes : List (Password × String)) (verifications : List Verified)
    (session : Prepared) : Preparation :=
  ⟨hashes.map (fun (password, hash) => (password.value, hash)), verifications, session⟩

/-- Verify `password` against `stored` (or the dummy hash): the same scrypt work either way. -/
def verifyPrepared (profile : Option String) (password : Password) (stored : Option String)
    (dummyHash : String) : IO Verified := do
  let accepted ← checkPassword password stored dummyHash
  pure ⟨profile, password.value, stored, accepted⟩

/-- The prepared hash of exactly this password, if the preparation computed one. -/
def Preparation.hashOf (preparation : Preparation) (password : Password) : Option String :=
  preparation.hashes.findSome? fun (value, hash) =>
    if LeanCrypto.constantTimeEq value.toUTF8 password.value.toUTF8 then some hash else none

/-- Accept only the prepared verdict for this profile, this password and this stored hash. A
credential that changed between preparation and admission is refused (`none`). -/
def Preparation.verdict (preparation : Preparation) (profile : String) (password : Password)
    (stored : Option String) : Bool :=
  preparation.verifications.any fun verified =>
    verified.accepted && verified.profile == some profile && verified.stored == stored &&
      LeanCrypto.constantTimeEq verified.password.toUTF8 password.value.toUTF8

/-- `Auth.startSession`: the session row, in the operation's own transaction. -/
def Storage.startSession {s Scope Profile E} [IsSchema s]
    {profile : LeanDb.Native.EntityStorage s Profile} (store : Storage s Profile profile)
    (env : Env) (prepared : Prepared) (reference : Ontology.Ref Profile) (ttl : Nat) :
    Native.CommandM Scope s E Unit := do
  let expires ← (Instant.ofEpochSeconds (Int.ofNat (env.now + ttl))).orAbort
    (fun _ => Native.fault "clock.invalid")
  insertPrivate store.session (store.sessionMake reference prepared.tokenDigest prepared.csrfDigest expires 1)

/-- Did this operation start the prepared session? Read inside its own transaction. -/
def Storage.started {s Profile} [IsSchema s] {profile : LeanDb.Native.EntityStorage s Profile}
    (store : Storage s Profile profile) (prepared : Prepared) : Read s Bool := do
  return (← store.sessionLookup prepared.tokenDigest).isSome

end LeanApi.Native.Auth
