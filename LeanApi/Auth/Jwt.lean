/-
  JWT (RFC 7519) with HS256 (RFC 7515 / 7518 §3.2).

  Verification, in order:
  1. Exactly three base64url segments, each strictly decoded.
  2. The header is a JSON object whose `alg` is in the allowed list, which
     is `["HS256"]`. `none` and every other algorithm are rejected before
     any signature work. `crit` is rejected (no extensions understood).
  3. The HMAC-SHA256 over `header.payload` equals the signature,
     compared in constant time.
  4. Claims: `exp` (required by default), `nbf`, `iat` (not in the future),
     each with `leeway` seconds; `iss` and `aud` when configured.

  The claims are then mapped to an actor by an app-supplied function; see
  `jwtBearer`. Keys shorter than 32 bytes are refused (RFC 7518 §3.2).
-/
import LeanApi.Auth.Basic
import LeanCrypto
import Lean.Data.Json

namespace LeanApi.Jwt

open Lean

inductive JwtError where
  | malformed (why : String)
  | algorithm (alg : String)
  | signature
  | expired
  | notYetValid
  | issuedInFuture
  | issuer
  | audience
  | missingClaim (name : String)
  | weakKey
  deriving Repr, BEq

instance : ToString JwtError where
  toString
    | .malformed w => s!"malformed token: {w}"
    | .algorithm a => s!"algorithm not allowed: {a}"
    | .signature => "bad signature"
    | .expired => "token expired"
    | .notYetValid => "token not yet valid"
    | .issuedInFuture => "token issued in the future"
    | .issuer => "wrong issuer"
    | .audience => "wrong audience"
    | .missingClaim n => s!"missing claim {n}"
    | .weakKey => "key shorter than 32 bytes"

structure Policy where
  /-- HMAC key; at least 32 bytes. -/
  key : ByteArray
  issuer : Option String := none
  audience : Option String := none
  leeway : Nat := 30
  requireExp : Bool := true
  /-- Maximum accepted lifetime (`exp - iat`) in seconds, if set. -/
  maxAge : Option Nat := none

private def segment (s : String) (what : String) : Except JwtError ByteArray :=
  match LeanCrypto.Base64Url.decode s with
  | some b => .ok b
  | none => .error (.malformed s!"{what} is not base64url")

private def jsonObj (b : ByteArray) (what : String) : Except JwtError Json := do
  let some s := String.fromUTF8? b | .error (.malformed s!"{what} is not UTF-8")
  match Json.parse s with
  | .ok j@(.obj _) => .ok j
  | .ok _ => .error (.malformed s!"{what} is not an object")
  | .error _ => .error (.malformed s!"{what} is not JSON")

private def numClaim (claims : Json) (name : String) : Except JwtError (Option Int) :=
  match claims.getObjVal? name with
  | .error _ => .ok none
  | .ok v => match v.getInt? with
    | .ok i => .ok (some i)
    | .error _ =>
      -- NumericDate may carry a fraction; truncate
      match v.getNum? with
      | .ok n => .ok (some (n.mantissa / (10 ^ n.exponent : Nat)))
      | .error _ => .error (.malformed s!"{name} is not a number")

/-- Verify `token` at unix time `now` (seconds); return the claims object. -/
def verify (p : Policy) (now : Nat) (token : String) : Except JwtError Json := do
  if p.key.size < 32 then throw .weakKey
  let [h, b, s] := token.splitOn "." | throw (.malformed "expected three segments")
  let header ← jsonObj (← segment h "header") "header"
  let alg := (header.getObjValAs? String "alg").toOption.getD ""
  if alg != "HS256" then throw (.algorithm (if alg.isEmpty then "(missing)" else alg))
  if (header.getObjVal? "crit").isOk then throw (.malformed "crit header not supported")
  let sig ← segment s "signature"
  let expected := LeanCrypto.hmacSha256 p.key s!"{h}.{b}".toUTF8
  unless LeanCrypto.constantTimeEq sig expected do throw .signature
  let claims ← jsonObj (← segment b "payload") "payload"
  let now : Int := now
  let lw : Int := p.leeway
  match ← numClaim claims "exp" with
  | some exp => if now - lw ≥ exp then throw .expired
  | none => if p.requireExp then throw (.missingClaim "exp")
  if let some nbf ← numClaim claims "nbf" then
    if now + lw < nbf then throw .notYetValid
  let iat? ← numClaim claims "iat"
  if let some iat := iat? then
    if now + lw < iat then throw .issuedInFuture
  if let some maxAge := p.maxAge then
    match iat?, ← numClaim claims "exp" with
    | some iat, some exp => if exp - iat > maxAge then throw (.malformed "lifetime exceeds maxAge")
    | _, _ => throw (.missingClaim "iat")
  if let some iss := p.issuer then
    if (claims.getObjValAs? String "iss").toOption != some iss then throw .issuer
  if let some aud := p.audience then
    let ok := match claims.getObjVal? "aud" with
      | .ok (.str a) => a == aud
      | .ok (.arr xs) => xs.any (· == Json.str aud)
      | _ => false
    unless ok do throw JwtError.audience
  return claims

/-- Sign claims with HS256. For issuing tokens in tests and simple apps. -/
def sign (key : ByteArray) (claims : Json) : String :=
  let h := LeanCrypto.Base64Url.encode (Json.mkObj [("alg", .str "HS256"), ("typ", .str "JWT")]).compress.toUTF8
  let b := LeanCrypto.Base64Url.encode claims.compress.toUTF8
  let sig := LeanCrypto.Base64Url.encode (LeanCrypto.hmacSha256 key s!"{h}.{b}".toUTF8)
  s!"{h}.{b}.{sig}"

/-- Seconds since the Unix epoch. -/
def unixNow : IO Nat := do
  let ts ← Std.Time.Timestamp.now
  return ts.toSecondsSinceUnixEpoch.val.toNat

end LeanApi.Jwt

namespace LeanApi

/-- A bearer authenticator that accepts HS256 JWTs under `policy` and maps
    verified claims to an actor with `toActor` (which may consult the
    database, e.g. to check the subject still exists). `clock` defaults to
    the system clock. -/
def jwtBearer (policy : Jwt.Policy) (toActor : Lean.Json → IO (Option actor))
    (clock : IO Nat := Jwt.unixNow) (realm : String := "api") : Authenticator actor where
  challenge := s!"Bearer realm=\"{realm}\""
  run req := do
    match req.header? "authorization" with
    | none => return .error .missing
    | some v =>
      if ((v.trimAscii.toString.splitOn " ").headD "").toLower != "bearer" then return .error .missing
      match bearerToken? req with
      | none => return .error (.invalid "malformed bearer token")
      | some tok =>
        match Jwt.verify policy (← clock) tok with
        | .error e => return .error (.invalid (toString e))
        | .ok claims =>
          match ← toActor claims with
          | some a => return .ok a
          | none => return .error (.invalid "unknown subject")

end LeanApi
