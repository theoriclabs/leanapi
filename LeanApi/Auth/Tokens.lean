/-
  Opaque bearer tokens and password verification.

  Tokens: 32 random bytes, base64url. The server stores only
  `digest token = hex (sha256 token)` and looks it up by that digest with
  an indexed equality query, never "load all tokens and compare". A leaked
  table of digests does not yield usable tokens. SHA-256 without salt is
  appropriate here because tokens are high-entropy random values (unlike
  passwords).

  Passwords: scrypt through `LeanCrypto.Password` (self-describing
  parameters, constant-time compare). `basicWithPasswords` builds a Basic
  authenticator from a lookup of the stored hash.
-/
import LeanApi.Auth.Basic
import LeanCrypto

namespace LeanApi.Tokens

/-- A fresh opaque token (256 bits). Return it to the client once. -/
def generate : IO String := do
  return LeanCrypto.Base64Url.encode (← LeanCrypto.randomBytes 32)

/-- What the server stores for a token. -/
def digest (token : String) : String := LeanCrypto.Hex.encode (LeanCrypto.sha256 token.toUTF8)

/-- Bearer authenticator: `lookupByDigest` should be an indexed lookup. -/
def bearerAuth (lookupByDigest : String → IO (Option actor)) (realm : String := "api") : Authenticator actor :=
  bearer (fun t => lookupByDigest (digest t)) realm

end LeanApi.Tokens

namespace LeanApi

/-- Hash a password for storage (scrypt, default parameters). -/
def hashPassword (pw : String) : IO String := LeanCrypto.Password.hash pw

def verifyPassword (pw stored : String) : Bool := LeanCrypto.Password.verify pw stored

/-- A precomputed hash verified against when the user does not exist, so
    unknown names cost the same scrypt work as wrong passwords. -/
def dummyHashFor (params : LeanCrypto.Password.Params := {}) : IO String :=
  LeanCrypto.Password.hash "leanapi-dummy-password" params

/-- Basic auth over stored scrypt hashes. `lookup name` returns the actor
    and its stored hash. Unknown users still pay one scrypt verification. -/
def basicWithPasswords (lookup : String → IO (Option (actor × String))) (dummy : String)
    (realm : String := "api") : Authenticator actor :=
  basic (realm := realm) fun user pw => do
    match ← lookup user with
    | some (a, stored) => return if verifyPassword pw stored then some a else none
    | none =>
      -- Keep the result in an observable IO branch. A discarded pure call
      -- is erased by the compiler, removing the dummy scrypt work.
      if verifyPassword pw dummy then IO.sleep 0
      return none

end LeanApi
