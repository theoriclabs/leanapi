import LeanApi
import LeanApi.Native

namespace AuthChecks
open LeanApi LeanDb Ontology Contract
open LeanApi.Native.Auth

structure Person where
  name : String
  email : String
  enabled : Bool
  deriving LeanDb.Entity
instance : HasTypeId Person := ⟨⟨"fixture", "Person"⟩⟩

structure Credential where
  person : LeanDb.Ref Person
  passwordHash : String
  deriving LeanDb.Entity
structure Session where
  person : LeanDb.Ref Person
  tokenDigest : String
  csrfDigest : String
  expiresAt : Int64
  revoked : Bool
  deriving LeanDb.Entity
unique% Credential.byPerson := person
unique% Session.byDigest := tokenDigest
schema% Database := Person, Credential, Session

private def must (value : Except ε α) : IO α := match value with
  | .ok value => pure value
  | .error _ => throw (IO.userError "auth fixture setup")
private def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def lookup (digest : String) : Read Database (Option (LiveSession Unit Person)) := do
  let some session ← Read.lookup Session Session.Unique.byDigest digest | return none
  let person ← Read.get Person session.val.person
  let row := person.bind fun person =>
    (LeanApi.Native.publicRef person.id).toOption.map fun id => LeanDb.Model.Trusted.row id person.val
  let .ok expiry := Ontology.Instant.ofEpochSeconds session.val.expiresAt.toInt | return none
  pure (some ⟨row, expiry, person.any (·.val.enabled), session.val.revoked, session.val.csrfDigest⟩)

/-- The signed-in profile of a mutation: a live session, Origin and CSRF for a cookie. -/
private def signedIn (config : CookieConfig) (env : Env) (req : Req)
    (lookup : String → Read Database (Option (LiveSession Unit Person))) :
    Read Database (Except (CallError Empty) (LeanDb.Model.Row Unit Person)) := do
  match ← resolve config env req lookup true with
  | .error e => return .error e
  | .ok none => return .error .unauthenticated
  | .ok (some row) => return .ok row

/-- A reader's profile: `none` with no credential, an error for a presented invalid one. -/
private def viewer (config : CookieConfig) (env : Env) (req : Req)
    (lookup : String → Read Database (Option (LiveSession Unit Person))) :
    Read Database (Except (CallError Empty) (Option (LeanDb.Model.Row Unit Person))) :=
  resolve config env req lookup

private def runRead (dc : DbConns) (read : Read Database α) : IO α := do
  must (← must (← DbM.run dc.writer.conn (Read.run read)))

def run : IO Unit := do
  let config ← must (CookieConfig.create "https://partiful.test")
  check (CookieConfig.create "http://partiful.test").toOption.isNone "production HTTPS"
  check (CookieConfig.create "http://external.test" true).toOption.isNone "development loopback only"
  let .ok password := Ontology.Password.parse " spaces Are Preserved! "
    | throw (IO.userError "password parser")
  let prepared ← prepare password
  check (prepared.passwordHash != password.value) "hash-only credentials"
  check (prepared.tokenDigest != (prepared.cookie config 60).value) "digest-only session token"
  check (← checkPassword password (some prepared.passwordHash) prepared.passwordHash) "correct password"
  let .ok wrong := Ontology.Password.parse "wrong Password Also Long" | throw (IO.userError "wrong parser")
  check (!(← checkPassword wrong (some prepared.passwordHash) prepared.passwordHash)) "wrong password"
  check (!(← checkPassword wrong none prepared.passwordHash)) "unknown account dummy verification"
  check ((Ontology.Email.parse "  ADA@Example.COM ").toOption.map (·.value) == some "ada@example.com")
    "shared canonical email parser"
  let token := (prepared.cookie config 60).value
  let req : Req := { method := .post, headers := [("cookie", s!"{config.name}={token}"),
    ("origin", config.origin), ("x-csrf-token", prepared.csrf)] }
  check ((originGuard config req).toOption == some ()) "same origin accepted"
  check ((csrfGuard prepared.csrfDigest req).toOption == some ()) "valid CSRF accepted"
  check (csrfGuard prepared.csrfDigest { req with headers := [("x-csrf-token", "bad")] }).toOption.isNone
    "invalid CSRF rejected"
  check (originGuard config { req with headers := [("origin", "https://evil.test")] }).toOption.isNone
    "cross origin rejected"
  check (cookieToken config { headers := [("cookie", s!"{config.name}=")] }).toOption.isNone
    "supplied empty cookie rejected"
  check (cookieToken config { headers := [("cookie", s!"{config.name}={token}; {config.name}={token}")] }).toOption.isNone
    "duplicate cookie rejected"
  let cookie := prepared.cookie config 60
  check (cookie.secure && cookie.httpOnly && cookie.sameSite == some .strict && cookie.domain.isNone && cookie.path == some "/")
    "production cookie protection"
  let csrfCookie := prepared.csrfCookie config 60
  check (csrfCookie.secure && !csrfCookie.httpOnly && csrfCookie.sameSite == some .strict &&
    csrfCookie.domain.isNone && csrfCookie.path == some "/" && csrfCookie.value == prepared.csrf &&
    csrfCookie.value != token) "readable same-origin CSRF cookie is separate from session credential"
  let receipt := (prepared.replyEdits config 60).apply (Res.json .null)
  check ((receipt.headerAll "set-cookie").length == 2) "auth receipt issues paired native cookies"
  let suffix ← Tokens.generate
  let dc ← DbConns.open s!".lake/test-db/auth-{suffix}.sqlite" (IsSchema.specs Database) 1
  try
    let person ← must (← DbM.run dc.writer.conn <| withTransaction do
      let person ← insert Person ⟨"Ada", "ada@example.com", true⟩
      discard <| insert Credential ⟨person.id, prepared.passwordHash⟩
      discard <| insert Session ⟨person.id, prepared.tokenDigest, prepared.csrfDigest, 100, false⟩
      pure person)
    let result ← runRead dc (signedIn config {now := 99} req lookup)
    check (result.toOption.map (·.id.key) == some (toString person.id.toInt64.toInt)) "live profile establishes actor"
    let anonymous ← runRead dc (viewer config {now := 99} {} lookup)
    check (match anonymous with | .ok none => true | _ => false) "absent credential anonymous"
    let invalid ← runRead dc (viewer config {now := 99} {headers := [("cookie", s!"{config.name}={suffix}")]} lookup)
    check invalid.toOption.isNone "supplied invalid session never anonymous"
    let expired ← runRead dc (signedIn config {now := 100} req lookup)
    check expired.toOption.isNone "exact session expiry cutoff"
    let csrfMissing ← runRead dc (signedIn config {now := 99} {req with headers := req.headers.filter (·.1 != "x-csrf-token")} lookup)
    check csrfMissing.toOption.isNone "missing CSRF fails mutation"
    let disabledPerson ← must (← DbM.run dc.writer.conn (update person {person.val with enabled := false}))
    let disabled ← runRead dc (signedIn config {now := 99} req lookup)
    check disabled.toOption.isNone "disabled live profile refused"
    let persisted ← must (← DbM.run dc.writer.conn (fetchAll Credential))
    check (persisted.size == 1 && persisted.any (fun row => row.val.passwordHash == prepared.passwordHash)) "persisted credential contains hash"
    let sessions ← must (← DbM.run dc.writer.conn (fetchAll Session))
    check (sessions.size == 1 && sessions.any (fun row => row.val.tokenDigest == prepared.tokenDigest && row.val.csrfDigest == prepared.csrfDigest))
      "persisted session digest-only"
    let some session := sessions[0]? | throw (IO.userError "nonempty session fixture")
    discard <| must (← DbM.run dc.writer.conn (update disabledPerson {disabledPerson.val with enabled := true}))
    discard <| must (← DbM.run dc.writer.conn (update session {session.val with revoked := true}))
    check (← runRead dc (signedIn config {now := 99} req lookup)).toOption.isNone "revoked session refused"
    discard <| must (← DbM.run dc.writer.conn (delete session.id))
    let some credential := persisted[0]? | throw (IO.userError "nonempty credential fixture")
    discard <| must (← DbM.run dc.writer.conn (delete credential.id))
    discard <| must (← DbM.run dc.writer.conn (delete person.id))
    check (← runRead dc (signedIn config {now := 99} req lookup)).toOption.isNone "deleted profile loses session authority"
    let maxId : LeanDb.Id Person := ⟨9223372036854775807⟩
    let publicId ← must (LeanApi.Native.publicRef maxId)
    check ((LeanApi.Native.nativeRef publicId).toOption.map (·.toInt64) == some maxId.toInt64) "max signed-64-bit nominal identity"
    check (LeanApi.Native.nativeRef publicId "another-space").toOption.isNone "scope mismatch refused"
    check (LeanApi.Native.publicRef (⟨-1⟩ : LeanDb.Id Person)).toOption.isNone "negative native identity refused"
    IO.println "PASS: native scrypt / profile session snapshot / expiry / origin / CSRF / nominal IDs"
  finally dc.close
end AuthChecks
