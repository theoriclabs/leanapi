/-
  Retry fingerprints computed by the framework (LAPI-10).

  A keyed request (`Idempotency-Key`) is replayed only if it is the same
  request. Whether it is the same is decided here, not by each endpoint:
  `Retry.fingerprintOf` hashes the request **as the endpoint reads it**:

  * the endpoint's identity (method and route template);
  * its path parameters;
  * the query parameters, sorted;
  * the body: JSON re-serialized canonically (keys sorted, no insignificant
    whitespace), anything else as its bytes;
  * `If-Match`, and every header the endpoint's signature declares
    (`Header n α`), except the key itself.

  A handler sees nothing of the request that this leaves out: `Auth` is the
  receipt's actor (part of its key), `Now` and `FreshToken` come from the
  environment. So the fingerprint cannot miss an input.

  The stored value is versioned (`v1:<hex>`). An app with receipts from
  before this change registers its old function (`LegacyFingerprint`): the
  old operation name and fingerprint, compared when the new ones find no
  receipt.

  The router passes the matched endpoint's identity and declared headers to
  the handler as two reserved path parameters (`Retry.routeParams`),
  appended after the template's own, so positional `Path` decoding and
  `Authenticates.authenticate_params` are unaffected.
-/
import LeanApi.Http.Request
import LeanApi.Http.Response
import LeanApi.Util.Base64
import LeanCrypto

namespace LeanApi

open Lean

/-- A keyed request's retry identity. -/
structure Retry where
  key : String
  /-- The endpoint: `"<METHOD> <template>"`. -/
  op : String
  /-- `v1:<hex sha256>` of the request as the endpoint reads it. -/
  fingerprint : String
  /-- The app's pre-`v1` operation name and fingerprint, if it registered one. -/
  legacy : Option (String × String) := none
  deriving Repr, BEq, DecidableEq

namespace Retry

/-- Reserved parameter names; a template parameter cannot contain NUL. -/
def routeKey : String := "\x00route"
def declaredKey : String := "\x00headers"

def isReserved (k : String) : Bool := k == routeKey || k == declaredKey

/-- What the router adds for an endpoint: its identity and declared headers. -/
def routeParams (method : Method) (template : String) (inputs : List String) : List (String × String) :=
  let declared := inputs.filterMap fun k =>
    if k.startsWith "header " then
      let n := (k.drop 7).toString
      some (if n.endsWith "?" then (n.dropEnd 1).toString else n)
    else none
  [(routeKey, s!"{method} {template}"), (declaredKey, ",".intercalate declared)]

/-- The endpoint identity the router passed, or the method and path. -/
def opOf (r : Req) : String :=
  (r.params.lookup routeKey).getD s!"{r.method} /{"/".intercalate r.path}"

def declaredOf (r : Req) : List String :=
  (((r.params.lookup declaredKey).getD "").splitOn ",").filter (!·.isEmpty)

/-- `1–255` visible ASCII characters. -/
def validKey (k : String) : Bool :=
  !k.isEmpty && k.length ≤ 255 && k.all fun c => c.toNat > 32 && c.toNat < 127

/-- The body as the endpoint reads it: canonical JSON when it is JSON,
    otherwise its bytes. -/
def canonicalBody (r : Req) : Json :=
  let raw := Json.mkObj [("bytes", .str (Base64.encode r.body))]
  if r.contentType? == some "application/json" then
    match String.fromUTF8? r.body with
    | some text => match Json.parse text with
      | .ok j => Json.mkObj [("json", j)]
      | .error _ => raw
    | none => raw
  else raw

private def insertSorted (x : String × String) : List (String × String) → List (String × String)
  | [] => [x]
  | y :: ys => if x.1 < y.1 || (x.1 == y.1 && x.2 ≤ y.2) then x :: y :: ys else y :: insertSorted x ys

private def sortPairs (xs : List (String × String)) : List (String × String) :=
  xs.foldr insertSorted []

private def pairs (xs : List (String × String)) : Json :=
  Json.arr (xs.map fun (k, v) => Json.arr #[.str k, .str v]).toArray

/-- The canonical form that is hashed. Unambiguous (a JSON array). -/
def canonical (op : String) (declared : List String) (r : Req) : String :=
  let headers := ("if-match" :: declared.map (·.toLower)).filter (· != "idempotency-key")
  let hs := headers.filterMap fun n => (r.header? n).map fun v => (n, v.trimAscii.toString)
  (Json.arr #[.str op, pairs (r.params.filter (!isReserved ·.1)), pairs (sortPairs r.query),
    canonicalBody r, pairs hs]).compress

/-- `v1:<hex sha256 (canonical …)>`. -/
def fingerprintOf (op : String) (declared : List String) (r : Req) : String :=
  "v1:" ++ LeanCrypto.Hex.encode (LeanCrypto.sha256 (canonical op declared r).toUTF8)

/-- The retry identity of `r` for endpoint `op`, when it carries a key. -/
def ofReq (op : String) (declared : List String) (key : String) (r : Req)
    (legacy : Option (String × String) := none) : Retry :=
  { key, op, fingerprint := fingerprintOf op declared r, legacy }

end Retry

/-- An app's pre-`v1` retry identity: the operation name and fingerprint it
    stored before the framework computed them. Default: none. -/
class LegacyFingerprint (σ : Type) where
  v0 : Req → Option (String × String)

instance (priority := low) : LegacyFingerprint σ := ⟨fun _ => none⟩

end LeanApi
