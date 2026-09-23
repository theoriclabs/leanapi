/-
  Requests. Like `Res`, a `Req` is plain data: the transport edge
  (`LeanApi.Server`) decodes the head, reads the body under the route's
  limit, and hands the handler a value. Path parameters are filled in by
  the router; `locals` carries strings set by middleware (request id,
  client address after proxy handling).
-/
import Std.Http
import LeanApi.Util.Url
import LeanApi.Http.Response

namespace LeanApi

open Std.Http

/-- Methods LeanAPI routes on. Anything else is answered 501 at the edge. -/
inductive Method where
  | get | head | post | put | patch | delete | options
  deriving Repr, DecidableEq, BEq, Hashable, Inhabited

namespace Method

def all : List Method := [.get, .head, .post, .put, .patch, .delete, .options]

def toString : Method → String
  | .get => "GET" | .head => "HEAD" | .post => "POST" | .put => "PUT"
  | .patch => "PATCH" | .delete => "DELETE" | .options => "OPTIONS"

instance : ToString Method := ⟨Method.toString⟩

def ofString? (s : String) : Option Method :=
  all.find? (·.toString == s.toUpper)

def ofStd? (m : Std.Http.Method) : Option Method := ofString? (ToString.toString m)

end Method

structure Req where
  method : Method := .get
  /-- Decoded path segments. `/a/b%2Fc` is `["a", "b/c"]`; `/` is `[]`. -/
  path : List String := []
  /-- The raw request target as received (still encoded), for logs. -/
  target : String := "/"
  /-- `true` when the raw path ended in `/` (and was not just `/`). -/
  trailingSlash : Bool := false
  /-- Decoded query pairs, in order. `?flag` is `("flag", "")`. -/
  query : List (String × String) := []
  /-- Header names lowercase; repeated headers appear repeatedly. -/
  headers : List (String × String) := []
  body : ByteArray := .empty
  /-- Filled by the router: template name ↦ decoded segment. -/
  params : List (String × String) := []
  /-- The peer address the socket reported, if any. -/
  remoteAddr : Option String := none
  /-- Strings set by middleware (`request-id`, `client-ip`, `scheme`, ...). -/
  locals : List (String × String) := []

instance : Inhabited Req := ⟨{}⟩

namespace Req

def header? (r : Req) (name : String) : Option String :=
  let n := name.toLower
  (r.headers.find? (·.1 == n)).map (·.2)

def headerAll (r : Req) (name : String) : List String :=
  let n := name.toLower
  (r.headers.filter (·.1 == n)).map (·.2)

def setHeader (r : Req) (name value : String) : Req :=
  let n := name.toLower
  { r with headers := (r.headers.filter (·.1 != n)) ++ [(n, value)] }

def param? (r : Req) (name : String) : Option String := r.params.lookup name
def query? (r : Req) (name : String) : Option String := r.query.lookup name
def queryAll (r : Req) (name : String) : List String :=
  (r.query.filter (·.1 == name)).map (·.2)

def local? (r : Req) (key : String) : Option String := r.locals.lookup key
def setLocal (r : Req) (key value : String) : Req :=
  { r with locals := (key, value) :: r.locals.filter (·.1 != key) }

/-- The request id set by the `requestId` middleware, or `"-"`. -/
def requestId (r : Req) : String := (r.local? "request-id").getD "-"

/-- The client address: set by `trustedProxy` when the peer is a trusted
    proxy, else the socket peer. -/
def clientAddr (r : Req) : Option String := (r.local? "client-addr") <|> r.remoteAddr

def bodyText? (r : Req) : Option String := String.fromUTF8? r.body

/-- The media type of `Content-Type`, lowercased, without parameters. -/
def contentType? (r : Req) : Option String :=
  (r.header? "content-type").map fun v => ((v.splitOn ";").headD "").trimAscii.toString.toLower

/-- Cookies from every `Cookie` header, in order. -/
def cookies (r : Req) : List (String × String) :=
  (r.headerAll "cookie").flatMap fun line =>
    (line.splitOn ";").filterMap fun part =>
      match (part.trimAscii.toString).splitOn "=" with
      | k :: vs@(_ :: _) =>
          let k := k.trimAscii.toString
          if k.isEmpty then none else some (k, "=".intercalate vs)
      | _ => none

def cookie? (r : Req) (name : String) : Option String := r.cookies.lookup name

/-- The path as it would be written, re-encoded: `/games/42`. -/
def pathString (r : Req) : String :=
  "/" ++ "/".intercalate (r.path.map Url.percentEncode) ++ (if r.trailingSlash then "/" else "")

/-- A test/direct-call constructor: parses `target` (path and query). -/
def mk' (method : Method) (target : String) (headers : List (String × String) := [])
    (body : ByteArray := .empty) : Req :=
  let (pathPart, queryPart) := match target.splitOn "?" with
    | p :: q :: rest => (p, "?".intercalate (q :: rest))
    | p :: [] => (p, "")
    | [] => ("/", "")
  let raw := (pathPart.splitOn "/").drop 1
  let trailing := raw.length > 1 && raw.getLast? == some ""
  let raw := if raw == [""] then [] else if trailing then raw.dropLast else raw
  let segs := raw.map fun s => (Url.percentDecode s).getD s
  { method, target, path := segs, trailingSlash := trailing
    query := (Url.parseForm queryPart).getD []
    headers := headers.map fun (k, v) => (k.toLower, v), body }

end Req

/-- An application: a request in, a response out. Handlers, routers, and
    middleware-wrapped stacks are all `App`s. -/
abbrev App := Req → IO Res

end LeanApi
