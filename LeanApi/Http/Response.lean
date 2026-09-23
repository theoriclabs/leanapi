/-
  Responses. A `Res` is plain data: status, header list, and a buffered
  body. It becomes a `Std.Http.Response` only at the transport edge
  (`Res.toStd`), so handlers, middleware, and the reference model can all
  compare and reason about responses as values.
-/
import Std.Http
import Lean.Data.Json

namespace LeanApi

open Std.Http Lean

/-- A response as a value. Header names are stored lowercase. -/
structure Res where
  status : Nat := 200
  headers : List (String × String) := []
  body : ByteArray := .empty

instance : Inhabited Res := ⟨{}⟩

namespace Res

/-- Replace every value of `name` with `value`. -/
def setHeader (r : Res) (name value : String) : Res :=
  let n := name.toLower
  { r with headers := (r.headers.filter (·.1 != n)) ++ [(n, value)] }

/-- Add a value of `name`, keeping existing ones (e.g. `set-cookie`, `vary`). -/
def addHeader (r : Res) (name value : String) : Res :=
  { r with headers := r.headers ++ [(name.toLower, value)] }

def header? (r : Res) (name : String) : Option String :=
  let n := name.toLower
  (r.headers.find? (·.1 == n)).map (·.2)

def headerAll (r : Res) (name : String) : List String :=
  let n := name.toLower
  (r.headers.filter (·.1 == n)).map (·.2)

def eraseHeader (r : Res) (name : String) : Res :=
  let n := name.toLower
  { r with headers := r.headers.filter (·.1 != n) }

def withStatus (r : Res) (s : Nat) : Res := { r with status := s }

def bodyText (r : Res) : String := String.fromUTF8? r.body |>.getD ""

def empty (status : Nat := 204) : Res := { status }

def text (s : String) (status : Nat := 200) : Res :=
  { status, headers := [("content-type", "text/plain; charset=utf-8")], body := s.toUTF8 }

def html (s : String) (status : Nat := 200) : Res :=
  { status, headers := [("content-type", "text/html; charset=utf-8")], body := s.toUTF8 }

def bytes (b : ByteArray) (contentType : String := "application/octet-stream") (status : Nat := 200) : Res :=
  { status, headers := [("content-type", contentType)], body := b }

def json (j : Json) (status : Nat := 200) : Res :=
  { status, headers := [("content-type", "application/json")], body := j.compress.toUTF8 }

def ofJson [ToJson α] (a : α) (status : Nat := 200) : Res := json (toJson a) status

def ok [ToJson α] (a : α) : Res := ofJson a 200
def created [ToJson α] (a : α) (location : Option String := none) : Res :=
  let r := ofJson a 201
  match location with
  | some l => r.setHeader "location" l
  | none => r

/-- Redirect. `status` is 301, 302, 303, 307 or 308. -/
def redirect (location : String) (status : Nat := 302) : Res :=
  (empty status).setHeader "location" location

def seeOther (location : String) : Res := redirect location 303

/-! ## Cookies -/

inductive SameSite where
  | strict | lax | none
  deriving Repr, BEq

structure Cookie where
  name : String
  value : String
  path : Option String := some "/"
  domain : Option String := none
  maxAge : Option Int := none
  httpOnly : Bool := true
  secure : Bool := true
  sameSite : Option SameSite := some .lax
  deriving Repr

/-- Cookie names are RFC 6265 tokens; values avoid `;`, `,`, whitespace,
    quotes and backslash. Invalid cookies are rejected, not escaped. -/
def Cookie.valid (c : Cookie) : Bool :=
  let tokenChar (ch : Char) := ch.toNat > 32 && ch.toNat < 127 && !"()<>@,;:\\\"/[]?={} ".contains ch
  let valueChar (ch : Char) := ch.toNat > 32 && ch.toNat < 127 && !";,\\\" ".contains ch
  !c.name.isEmpty && c.name.all tokenChar && c.value.all valueChar

def Cookie.render (c : Cookie) : String := Id.run do
  let mut s := s!"{c.name}={c.value}"
  if let some p := c.path then s := s ++ s!"; Path={p}"
  if let some d := c.domain then s := s ++ s!"; Domain={d}"
  if let some m := c.maxAge then s := s ++ s!"; Max-Age={m}"
  if c.httpOnly then s := s ++ "; HttpOnly"
  if c.secure then s := s ++ "; Secure"
  match c.sameSite with
  | some .strict => s := s ++ "; SameSite=Strict"
  | some .lax => s := s ++ "; SameSite=Lax"
  | some .none => s := s ++ "; SameSite=None"
  | none => pure ()
  return s

/-- Add a `Set-Cookie`. Panics are avoided: an invalid cookie is dropped
    and the response becomes a 500, so it is noticed in tests. -/
def setCookie (r : Res) (c : Cookie) : Res :=
  if c.valid then r.addHeader "set-cookie" c.render
  else { status := 500, headers := [("content-type", "text/plain; charset=utf-8")],
         body := "invalid cookie".toUTF8 }

def clearCookie (r : Res) (name : String) (path : String := "/") : Res :=
  r.setCookie { name, value := "", path := some path, maxAge := some 0 }

end Res

/-! ## Problem details (RFC 9457) -/

/-- An error response body. `extensions` carries field-level detail such
    as validation errors. `internal` is never sent: it is logged under the
    request id. -/
structure Problem where
  status : Nat
  title : String
  detail : Option String := none
  type : String := "about:blank"
  extensions : List (String × Json) := []
  headers : List (String × String) := []
  internal : Option String := none

instance : Inhabited Problem := ⟨{ status := 500, title := "Internal Server Error" }⟩

namespace Problem

def reason : Nat → String
  | 400 => "Bad Request" | 401 => "Unauthorized" | 403 => "Forbidden"
  | 404 => "Not Found" | 405 => "Method Not Allowed" | 406 => "Not Acceptable"
  | 408 => "Request Timeout" | 409 => "Conflict" | 410 => "Gone"
  | 412 => "Precondition Failed" | 413 => "Content Too Large"
  | 415 => "Unsupported Media Type" | 422 => "Unprocessable Content"
  | 428 => "Precondition Required" | 429 => "Too Many Requests"
  | 500 => "Internal Server Error" | 501 => "Not Implemented"
  | 503 => "Service Unavailable" | 504 => "Gateway Timeout"
  | _ => "Error"

def make (status : Nat) (detail : Option String := none) : Problem :=
  { status, title := reason status, detail }

def badRequest (d : String) : Problem := make 400 (some d)
def notFound : Problem := make 404
def forbidden : Problem := make 403
def conflict (d : String) : Problem := make 409 (some d)
def serverError (why : String) : Problem := { make 500 with internal := some why }

def withHeader (p : Problem) (k v : String) : Problem :=
  { p with headers := p.headers ++ [(k.toLower, v)] }

def withExt (p : Problem) (k : String) (v : Json) : Problem :=
  { p with extensions := p.extensions ++ [(k, v)] }

def toJson (p : Problem) : Json :=
  let base : List (String × Json) :=
    [("type", .str p.type), ("title", .str p.title), ("status", Json.num p.status)]
  let base := match p.detail with
    | some d => base ++ [("detail", .str d)]
    | none => base
  Json.mkObj (base ++ p.extensions)

def toRes (p : Problem) : Res :=
  { status := p.status
    headers := [("content-type", "application/problem+json")] ++ p.headers
    body := p.toJson.compress.toUTF8 }

end Problem

/-! ## Transport edge -/

/-- Status for a code; unknown codes in a valid range become a custom status. -/
def statusOf (n : Nat) : Status :=
  (Status.ofCode none n.toUInt16).getD .internalServerError

/-- Convert to the transport's response. Invalid header names or values are
    dropped rather than sent (the transport would reject them anyway). -/
def Res.toStd (r : Res) : Std.Async.Async (Response Body.Any) := do
  let headers := r.headers.foldl (init := Headers.empty) fun acc (k, v) =>
    match Header.Name.ofString? k, Header.Value.ofString? v with
    | some n, some val => acc.insert n val
    | _, _ => acc
  let resp ← (Response.new.status (statusOf r.status) |>.headers headers).fromBytes r.body
  return { line := resp.line, body := Body.Any.ofBody resp.body, extensions := resp.extensions }

end LeanApi
