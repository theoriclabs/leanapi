/-
  Authentication interface (M1.5).

  An `Authenticator actor` reads the request head and either produces an
  actor, says no credentials were presented, or rejects the credentials.

  Contract (docs/decisions/0003-authenticator-contract.md): an accepted
  credential establishes only that the request carried a credential the
  app's verifier accepted, and that the verifier mapped it to this actor.
  It does NOT establish that a particular human sent the request, that the
  actor still holds any role, or anything about the body. Authorization is
  a separate, later decision made against current domain state.

  401 carries `WWW-Authenticate` for each scheme the route accepts. 403 is
  for authenticated actors denied by policy and is never produced here.
-/
import LeanApi.Http.Extract
import LeanApi.Util.Base64

namespace LeanApi

inductive AuthFailure where
  /-- No credentials for this authenticator's scheme were presented. -/
  | missing
  /-- Credentials were presented and rejected. The string is for logs only. -/
  | invalid (why : String)
  deriving Repr, BEq, Inhabited

structure Authenticator (actor : Type) where
  /-- The `WWW-Authenticate` challenge, e.g. `Bearer realm="api"`. -/
  challenge : String
  run : Req → IO (Except AuthFailure actor)

namespace Authenticator

/-- Try `a`; when it finds no credentials of its scheme, try `b`. A present
    but invalid credential is final (no fallthrough to a weaker scheme). -/
def orElse (a b : Authenticator actor) : Authenticator actor where
  challenge := a.challenge ++ ", " ++ b.challenge
  run req := do
    match ← a.run req with
    | .error .missing => b.run req
    | r => pure r

def anyOf : List (Authenticator actor) → Authenticator actor
  | [] => { challenge := "", run := fun _ => pure (.error .missing) }
  | [a] => a
  | a :: rest => a.orElse (anyOf rest)

def map (a : Authenticator α) (f : α → β) : Authenticator β :=
  { challenge := a.challenge, run := fun r => do return (← a.run r).map f }

/-- Post-verification mapping that may fail (e.g. claims → actor lookup). -/
def bindIO (a : Authenticator α) (f : α → IO (Except AuthFailure β)) : Authenticator β :=
  { challenge := a.challenge
    run := fun r => do
      match ← a.run r with
      | .ok x => f x
      | .error e => pure (.error e) }

end Authenticator

def unauthorized (challenge : String) (detail : String := "authentication required") : Res :=
  let p := Problem.make 401 (some detail)
  (if challenge.isEmpty then p else p.withHeader "www-authenticate" challenge).toRes

/-- Require an actor. Missing or invalid credentials: 401 with challenge. -/
def requireAuth (a : Authenticator actor) (h : actor → App) : App := fun req => do
  match ← a.run req with
  | .ok who => h who req
  | .error .missing => pure (unauthorized a.challenge)
  | .error (.invalid _) => pure (unauthorized a.challenge "invalid credentials")

/-- Optional: no credentials is `none`; invalid credentials are still 401,
    so a bad token is never silently treated as anonymous. -/
def optionalAuth (a : Authenticator actor) (h : Option actor → App) : App := fun req => do
  match ← a.run req with
  | .ok who => h (some who) req
  | .error .missing => h none req
  | .error (.invalid _) => pure (unauthorized a.challenge "invalid credentials")

/-! ## Credential extraction -/

/-- The token of `Authorization: Bearer <token>`. The scheme is
    case-insensitive; the token must be nonempty token68. -/
def bearerToken? (req : Req) : Option String := do
  let v ← req.header? "authorization"
  let parts := (v.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  match parts with
  | [scheme, tok] =>
    if scheme.toLower == "bearer" && tok.toList.all (fun (c : Char) => c.isAlphanum || "-._~+/=".contains c) then some tok else none
  | _ => none

/-- `Authorization: Basic base64(user:pass)`. `none` if absent or malformed.
    Passwords may contain `:`; user names may not (RFC 7617). -/
def basicCredentials? (req : Req) : Option (String × String) := do
  let v ← req.header? "authorization"
  let parts := (v.trimAscii.toString.splitOn " ").filter (!·.isEmpty)
  match parts with
  | [scheme, enc] =>
    if scheme.toLower != "basic" then none else
    let bytes ← Base64.decode enc
    let s ← String.fromUTF8? bytes
    match s.splitOn ":" with
    | user :: rest@(_ :: _) => some (user, ":".intercalate rest)
    | _ => none
  | _ => none

private def hasScheme (req : Req) (scheme : String) : Bool :=
  match req.header? "authorization" with
  | some v => ((v.trimAscii.toString.splitOn " ").headD "").toLower == scheme
  | none => false

/-- A bearer authenticator over an app-supplied verifier (token lookup,
    JWT verification, ...). -/
def bearer (verify : String → IO (Option actor)) (realm : String := "api") : Authenticator actor where
  challenge := s!"Bearer realm=\"{realm}\""
  run req := do
    if !hasScheme req "bearer" then return .error .missing
    match bearerToken? req with
    | none => return .error (.invalid "malformed bearer token")
    | some t =>
      match ← verify t with
      | some a => return .ok a
      | none => return .error (.invalid "token rejected")

/-- A Basic authenticator over an app-supplied password check. -/
def basic (verify : String → String → IO (Option actor)) (realm : String := "api") : Authenticator actor where
  challenge := s!"Basic realm=\"{realm}\", charset=\"UTF-8\""
  run req := do
    if !hasScheme req "basic" then return .error .missing
    match basicCredentials? req with
    | none => return .error (.invalid "malformed basic credentials")
    | some (u, p) =>
      match ← verify u p with
      | some a => return .ok a
      | none => return .error (.invalid "credentials rejected")

/-- A cookie-held session token (e.g. set at login). -/
def sessionCookie (name : String) (verify : String → IO (Option actor)) : Authenticator actor where
  challenge := ""
  run req := do
    match req.cookie? name with
    | none => return .error .missing
    | some t =>
      match ← verify t with
      | some a => return .ok a
      | none => return .error (.invalid "session rejected")

end LeanApi
