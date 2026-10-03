import LeanApiDomain.Auth
import LeanApiDomain.NativeStorage

namespace LeanApi.Domain.Auth
open LeanApi LeanDb LeanApp.Domain Ontology

/-- Coherent native capabilities generated with the schema. Credentials and
sessions are private storage, never contracts or an extra authentication API. -/
structure Storage (s Profile : Type) [IsSchema s]
    (profile : LeanDb.Domain.EntityStorage s Profile) : Type 1 where
  Credential : Type
  credential : LeanDb.Domain.EntityStorage s Credential
  credentialMake : LeanApp.Domain.Ref Profile → String → Nat → Credential
  credentialHash : Credential → String
  credentialVersion : Credential → Nat
  credentialEnabled : Credential → Bool
  credentialLookup : LeanApp.Domain.Ref Profile → Read s (Option Credential)
  Session : Type
  session : LeanDb.Domain.EntityStorage s Session
  sessionMake : LeanApp.Domain.Ref Profile → String → String → Instant → Nat → Session
  sessionProfile : Session → LeanApp.Domain.Ref Profile
  sessionExpires : Session → Instant
  sessionRevoked : Session → Bool
  sessionCSRF : Session → String
  sessionVersion : Session → Nat
  sessionLookup : String → Read s (Option Session)
  revoke : {Scope E : Type} → String → Native.CommandM Scope s E Unit
  /-- Milestone 1's generated sign-in looks the profile up by its unique email. An authored
  sign-in does its own lookup in the flow, so authored storage leaves this empty. -/
  profileLookup : Email → Read s (Contract.CallResult (Option (LeanApp.Domain.Ref Profile × Profile)) Empty) :=
    fun _ => pure (.ok none)
  /-- Milestone 1's generated credential carries a version and an enabled flag that every
  session check rereads. An authored `Credential` (DDD-LAPI-06) has neither, so its sessions
  are checked on their own row: digest, expiry, revocation and the live profile. -/
  checksCredential : Bool := true

class HasStorage (s Profile : Type) [schema : outParam (IsSchema s)]
    (profile : outParam (LeanDb.Domain.EntityStorage s Profile)) : Type 1 where
  storage : Storage s Profile profile

private def insertPrivate {s Scope T E} [IsSchema s]
    (storage : LeanDb.Domain.EntityStorage s T) (value : T) : Native.CommandM Scope s E Unit :=
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

def Storage.live {s Profile Scope} [IsSchema s] [LeanApp.Domain.Entity Profile]
    {profile : LeanDb.Domain.EntityStorage s Profile} (store : Storage s Profile profile)
    (digest : String) : Read s (Option (LiveSession Scope Profile)) := do
  let some session ← store.sessionLookup digest | return none
  let reference := store.sessionProfile session
  let enabled ← if !store.checksCredential then pure true else do
    let some credential ← store.credentialLookup reference | return none
    if store.credentialVersion credential != store.sessionVersion session then return none
    pure (store.credentialEnabled credential)
  match profile.find reference with
  | .error _ => return none
  | .ok program =>
    let live ← program
    return some { profile := live
                  expiresAt := store.sessionExpires session
                  enabled := enabled
                  revoked := store.sessionRevoked session
                  csrfDigest := store.sessionCSRF session }

/-- Type-0 preparation attestation; only native preparation constructs it. It
does not contain authority, and final lookup/version checks still run in Txn. -/
structure Admission where
  private mk ::
  prepared : Prepared
  private password : String
  private address : Option String
  private version : Option Nat
  private accepted : Bool

def prepareSignUp (password : Password) : IO Admission := do
  pure ⟨← prepare password, password.value, none, none, true⟩

def prepareSignIn (address : Email) (password : Password)
    (candidate : Option (String × Nat)) (dummyHash : String) : IO Admission := do
  let accepted ← checkPassword password (candidate.map Prod.fst) dummyHash
  let prepared ← prepareSession (candidate.map Prod.fst |>.getD dummyHash)
  pure ⟨prepared, password.value, some address.value, candidate.map Prod.snd, accepted⟩

def Storage.candidate {s Profile} [IsSchema s]
    {profile : LeanDb.Domain.EntityStorage s Profile} (store : Storage s Profile profile)
    (address : Email) : Read s (Contract.CallResult (Option (String × Nat)) Empty) := do
  match ← store.profileLookup address with
  | .error error => return .error error
  | .ok none => return .ok none
  | .ok (some (reference, _)) =>
    let some credential ← store.credentialLookup reference | return .ok none
    if !store.credentialEnabled credential then return .ok none
    return .ok (some (store.credentialHash credential, store.credentialVersion credential))

private def issue {s Scope Profile E} [IsSchema s]
    {profile : LeanDb.Domain.EntityStorage s Profile} (store : Storage s Profile profile)
    (env : Env) (admission : Admission) (reference : LeanApp.Domain.Ref Profile) (version ttl : Nat) :
    Native.CommandM Scope s E Unit := do
  let expires ← (Instant.ofEpochSeconds (Int.ofNat (env.now + ttl))).orAbort
    (fun _ => Native.fault "clock.invalid")
  insertPrivate store.session (store.sessionMake reference admission.prepared.tokenDigest
    admission.prepared.csrfDigest expires version)

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
    {profile : LeanDb.Domain.EntityStorage s Profile} (store : Storage s Profile profile)
    (env : Env) (prepared : Prepared) (reference : LeanApp.Domain.Ref Profile) (ttl : Nat) :
    Native.CommandM Scope s E Unit := do
  let expires ← (Instant.ofEpochSeconds (Int.ofNat (env.now + ttl))).orAbort
    (fun _ => Native.fault "clock.invalid")
  insertPrivate store.session (store.sessionMake reference prepared.tokenDigest prepared.csrfDigest expires 1)

/-- Did this operation start the prepared session? Read inside its own transaction. -/
def Storage.started {s Profile} [IsSchema s] {profile : LeanDb.Domain.EntityStorage s Profile}
    (store : Storage s Profile profile) (prepared : Prepared) : Read s Bool := do
  return (← store.sessionLookup prepared.tokenDigest).isSome

def Storage.signUp {s Scope Profile E} [IsSchema s] [LeanApp.Domain.Entity Profile]
    {profile : LeanDb.Domain.EntityStorage s Profile} (store : Storage s Profile profile)
    (env : Env) (admission : Admission) (value : Profile) (password : Password)
    (constraints : List (LeanApp.Domain.Constraint E)) (ttl : Nat) :
    Native.CommandM Scope s E (LeanApp.Domain.Ref Profile) := do
  if admission.address.isSome || !admission.accepted || password.value != admission.password then
    Txn.throw (Native.fault "auth.preparation_mismatch")
  let reference ← Native.create profile value constraints
  insertPrivate store.credential (store.credentialMake reference admission.prepared.passwordHash 1)
  issue store env admission reference 1 ttl
  return reference

def Storage.signIn {s Scope Profile E} [IsSchema s]
    {profile : LeanDb.Domain.EntityStorage s Profile} (store : Storage s Profile profile)
    (env : Env) (admission : Admission) (address : Email) (password : Password)
    (invalidCredentials : E) (ttl : Nat) : Native.CommandM Scope s E (LeanApp.Domain.Ref Profile) := do
  if !admission.accepted || admission.address != some address.value ||
      password.value != admission.password then Txn.throw (.domain invalidCredentials)
  let found ← (Txn.ofRead (store.profileLookup address)).orAbort (Contract.CallError.mapDomain Empty.elim)
  let some (reference, _) := found | Txn.throw (.domain invalidCredentials)
  let some credential ← Txn.ofRead (store.credentialLookup reference)
    | Txn.throw (.domain invalidCredentials)
  if !store.credentialEnabled credential || admission.version != some (store.credentialVersion credential) ||
      admission.prepared.passwordHash != store.credentialHash credential then
    Txn.throw (.domain invalidCredentials)
  issue store env admission reference (store.credentialVersion credential) ttl
  return reference

end LeanApi.Domain.Auth
