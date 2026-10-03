import LeanApi.Auth.Tokens
import LeanApi.Http.DbEndpoint
import LeanApp.Domain.Flow
import LeanApiDomain.Contract

/-! Profile-session boundary using LeanAPI's existing scrypt and opaque token implementation.
The schema-derived credential/session store supplies live rows in the operation snapshot.
These helpers are native-only and have no public Wire instances. -/
namespace LeanApi.Domain.Auth
open LeanApi LeanDb LeanApp.Domain Contract Ontology

structure CookieConfig where
  private mk ::
  origin : String
  development : Bool

def CookieConfig.create (origin : String) (development : Bool := false) : Validation CookieConfig := do
  let some uri := Std.Http.URI.parse? origin | Validation.fail "auth.invalid_origin"
  let some authority := uri.authority | Validation.fail "auth.invalid_origin"
  if authority.userInfo.isSome || origin.contains '?' || origin.contains '#' ||
      toString uri.path != "" || (toString authority.host).isEmpty then
    Validation.fail "auth.invalid_origin"
  if development then
    if toString uri.scheme != "http" ||
        !["localhost", "127.0.0.1", "[::1]"].contains (toString authority.host) then
      Validation.fail "auth.development_requires_loopback"
  else if toString uri.scheme != "https" then Validation.fail "auth.https_required"
  pure ⟨origin, development⟩

def CookieConfig.name (config : CookieConfig) : String :=
  if config.development then "leanapp_session" else "__Host-leanapp_session"

def CookieConfig.csrfName (config : CookieConfig) : String :=
  if config.development then "leanapp_csrf" else "__Host-leanapp_csrf"

def tokenShape (token : String) : Bool :=
  token.length == 43 && token.toList.all fun c =>
    c.toNat < 128 && (c.isAlphanum || c == '_' || c == '-')

private def cookieEntries (config : CookieConfig) (req : Req) : List (List String) :=
  let entries := (req.headerAll "cookie").flatMap fun header =>
    header.splitOn ";" |>.map (fun item => item.trimAscii.toString.splitOn "=")
  entries.filter fun parts => (parts.headD "").trimAscii.toString == config.name

/-- Missing and supplied-invalid are distinct, including duplicate/malformed cookies. -/
def cookieToken (config : CookieConfig) (req : Req) : Except (CallError Empty) (Option String) :=
  match cookieEntries config req with
  | [] => .ok none
  | [[_, token]] => if tokenShape token then .ok (some token) else .error .unauthenticated
  | _ => .error .unauthenticated

/-- `Authorization: Bearer <token>` for non-browser clients. Missing is `none`. Anything
else that is supplied (another scheme, a repeated header, a malformed token) is refused. -/
def bearerToken (req : Req) : Except (CallError Empty) (Option String) :=
  match req.headerAll "authorization" with
  | [] => .ok none
  | [value] =>
    match value.splitOn " " with
    | [scheme, token] =>
      if scheme.toLower == "bearer" && tokenShape token then .ok (some token) else .error .unauthenticated
    | _ => .error .unauthenticated
  | _ => .error .unauthenticated

/-- The session credential a request presents. Browsers send the HttpOnly cookie, which
the browser attaches by itself; other clients send a bearer token, which it never does. -/
inductive Presented where
  | none
  | cookie (token : String)
  | bearer (token : String)
  deriving BEq

def Presented.token? : Presented → Option String
  | .none => Option.none
  | .cookie token | .bearer token => some token

def Presented.isBearer : Presented → Bool
  | .bearer _ => true
  | _ => false

/-- A request may present one session transport. Both at once is a malformed request. -/
def ambiguousCredentials : CallError Empty := .protocol ⟨"auth.ambiguous_credentials", some 400, ""⟩

def presented (config : CookieConfig) (req : Req) : Except (CallError Empty) Presented :=
  let cookieSupplied := !(cookieEntries config req).isEmpty
  let bearerSupplied := !(req.headerAll "authorization").isEmpty
  if cookieSupplied && bearerSupplied then .error ambiguousCredentials
  else if bearerSupplied then
    match bearerToken req with
    | .error error => .error error
    | .ok none => .ok .none
    | .ok (some token) => .ok (.bearer token)
  else
    match cookieToken config req with
    | .error error => .error error
    | .ok none => .ok .none
    | .ok (some token) => .ok (.cookie token)

/-- The explicit token request of sign-up and sign-in: the raw token is returned in that
one response body instead of a cookie. Browsers never send this media type by default. -/
def tokenMediaType : String := "application/vnd.leanapp.token"

def tokenRequested (req : Req) : Bool :=
  (req.headerAll "accept").any fun line => (line.splitOn ",").any fun range =>
    ((range.splitOn ";").headD "").trimAscii.toString.toLower == tokenMediaType

/-- For anonymous sign-up/sign-in and session-authenticated commands. Never trust Host
or forwarded headers to choose the allowed browser origin. -/
def originGuard (config : CookieConfig) (req : Req) : Except (CallError Empty) Unit :=
  if req.headerAll "origin" == [config.origin] then .ok () else .error .forbidden

/-- Anonymous commands keep the exact browser Origin check, except for a request that
presents a bearer token, or that asks for a token reply and carries no session cookie
(it then receives no cookie, so there is nothing for a cross-site page to plant). -/
def anonymousGuard (config : CookieConfig) (req : Req) (tokenReply : Bool := false) :
    Except (CallError Empty) Unit :=
  match presented config req with
  | .error error => .error error
  | .ok (.bearer _) => .ok ()
  | .ok .none => if tokenReply then .ok () else originGuard config req
  | .ok (.cookie _) => originGuard config req

/-- The expected CSRF value is digest-only storage. A missing header fails closed. -/
def csrfGuard (expectedDigest : String) (req : Req) : Except (CallError Empty) Unit :=
  match req.headerAll "x-csrf-token" with
  | [token] =>
    if tokenShape token && LeanCrypto.constantTimeEq (Tokens.digest token).toUTF8 expectedDigest.toUTF8
    then .ok () else .error .forbidden
  | _ => .error .forbidden

/-- Native storage supplies profile state and generation/revocation checks inside this
request's snapshot. The profile is optional so a dangling/deleted reference is refused. -/
structure LiveSession (Scope Profile : Type) where
  profile : Option (Row Scope Profile)
  expiresAt : Instant
  enabled : Bool
  revoked : Bool
  csrfDigest : String

/-- No authority cache: invoke `lookup` in the same Read/Txn as the flow. Cookie and
bearer sessions share one table, digest, expiry, revocation and version check. Only the
cookie, an ambient credential, needs the Origin and CSRF checks on a mutation. -/
def resolve {s : Type} [IsSchema s] (config : CookieConfig) (env : Env) (req : Req)
    (lookup : String → Read s (Option (LiveSession Scope Profile)))
    (mutation : Bool := false) : Read s (Except (CallError Empty) (Option (Row Scope Profile))) := do
  let credential ← match presented config req with
    | .error e => return .error e
    | .ok credential => pure credential
  let some token := credential.token? | return .ok none
  let some session ← lookup (Tokens.digest token) | return .error .unauthenticated
  if !session.enabled || session.revoked || session.expiresAt.value ≤ (env.now : Int) then
    return .error .unauthenticated
  let some profile := session.profile | return .error .unauthenticated
  if mutation && !credential.isBearer then
    match originGuard config req, csrfGuard session.csrfDigest req with
    | .error e, _ | _, .error e => return .error e
    | .ok _, .ok _ => pure ()
  return .ok (some profile)

def signedIn {s : Type} [IsSchema s] (config : CookieConfig) (env : Env) (req : Req)
    (lookup : String → Read s (Option (LiveSession Scope Profile))) :
    Read s (Except (CallError Empty) (SignedIn Scope Profile)) := do
  match ← resolve config env req lookup true with
  | .error e => return .error e
  | .ok none => return .error .unauthenticated
  | .ok (some profile) => return .ok (Trusted.signedIn profile)

def viewer {s : Type} [IsSchema s] (config : CookieConfig) (env : Env) (req : Req)
    (lookup : String → Read s (Option (LiveSession Scope Profile))) :
    Read s (Except (CallError Empty) (Viewer Scope Profile)) := do
  return (← resolve config env req lookup).map Trusted.viewer

/-- Native result only. No Repr/ToJson/Wire: a raw session token is delivered through
`Set-Cookie`, or in the one response body of an explicit token request (`tokenEdits`).
Hashing and randomness happen outside the writer critical section. -/
structure Prepared where
  private mk ::
  passwordHash : String
  tokenDigest : String
  csrfDigest : String
  private token : String
  csrf : String

def prepare (password : Password) : IO Prepared := do
  let hash ← hashPassword password.value
  let token ← Tokens.generate
  let csrf ← Tokens.generate
  pure ⟨hash, Tokens.digest token, Tokens.digest csrf, token, csrf⟩

/-- Reuse the existing token generator without doing a second scrypt hash. -/
def prepareSession (hash : String) : IO Prepared := do
  let token ← Tokens.generate
  let csrf ← Tokens.generate
  pure ⟨hash, Tokens.digest token, Tokens.digest csrf, token, csrf⟩

/-- Preserve bytes; unknown account uses the existing dummy hash and the same KDF. -/
def checkPassword (password : Password) (stored : Option String) (dummyHash : String) : IO Bool := do
  let accepted := verifyPassword password.value (stored.getD dummyHash)
  -- Keep dummy verification observable to the native optimizer, as basicWithPasswords does.
  if accepted then IO.sleep 0
  pure (stored.isSome && accepted)

def Prepared.cookie (prepared : Prepared) (config : CookieConfig) (ttl : Nat) : Res.Cookie :=
  { name := config.name, value := prepared.token, secure := !config.development,
    httpOnly := true, sameSite := some .strict, maxAge := some ttl }

/-- Same-origin browser-readable CSRF material survives refresh. It is never the
session credential; mutations still verify Origin and the stored CSRF digest. -/
def Prepared.csrfCookie (prepared : Prepared) (config : CookieConfig) (ttl : Nat) : Res.Cookie :=
  { name := config.csrfName, value := prepared.csrf, secure := !config.development,
    httpOnly := false, sameSite := some .strict, maxAge := some ttl }

def Prepared.replyEdits (prepared : Prepared) (config : CookieConfig) (ttl : Nat) :
    LeanApi.Domain.ReplyEdits :=
  { headers := [("x-leanapp-auth-csrf", prepared.csrf)]
    cookies := [prepared.cookie config ttl, prepared.csrfCookie config ttl] }

/-- Explicit token reply for a non-browser client: no cookie, no CSRF material. The success
value becomes `{"profile": <ref>, "token": <raw>}`; the token appears nowhere else. -/
def Prepared.tokenEdits (prepared : Prepared) : LeanApi.Domain.ReplyEdits :=
  { value := some fun profile => .mkObj [("profile", profile), ("token", .str prepared.token)] }

end LeanApi.Domain.Auth
