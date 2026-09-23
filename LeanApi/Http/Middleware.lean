/-
  Middleware, Express-style: a middleware is `App → App`. It may
  short-circuit, rewrite the request, rewrite the response, or run effects.

  Decision record 0001 (Q8, v0.1 form): middleware is TRUSTED adapter
  code. No theorem about a handler covers what middleware does; any claim
  about exported routes lists the middleware stack as an assumption.
  `Stack.describe` prints the effective order so the assumption is
  inspectable.

  Order: `Stack.of [a, b, c]` runs `a` outermost: a request passes
  a → b → c → app, and the response returns c → b → a.
-/
import LeanApi.Http.Router
import Std.Async

namespace LeanApi

abbrev Middleware := App → App

structure NamedMiddleware where
  name : String
  run : Middleware

/-- An ordered, named list of middleware. -/
structure Stack where
  layers : List NamedMiddleware := []

namespace Stack

def of (layers : List NamedMiddleware) : Stack := ⟨layers⟩

def push (s : Stack) (name : String) (mw : Middleware) : Stack := ⟨s.layers ++ [⟨name, mw⟩]⟩

/-- Wrap `app`: the first layer is outermost. -/
def apply (s : Stack) (app : App) : App := s.layers.foldr (fun l acc => l.run acc) app

def describe (s : Stack) : String :=
  " → ".intercalate (s.layers.map (·.name) ++ ["app"])

end Stack

/-! ## Built-ins -/

/-- Convert exceptions from the inner app into a 500 `problem+json` without
    internal details. The exception text is logged with the request id. -/
def recover (log : String → IO Unit := IO.eprintln) : NamedMiddleware :=
  ⟨"recover", fun h req => do
    try h req
    catch e =>
      log s!"\{\"event\":\"error\",\"request_id\":\"{req.requestId}\",\"error\":{Lean.Json.str (toString e) |>.compress}}"
      pure ((Problem.make 500).withExt "request_id" (.str req.requestId)).toRes⟩

private def hexOf (n : Nat) (width : Nat) : String :=
  let s := String.ofList (Nat.toDigits 16 n)
  "".pushn '0' (width - s.length) ++ s

/-- A random request id (128 bits, hex). -/
def freshRequestId : IO String := do
  let mut s := ""
  for _ in [0:4] do
    s := s ++ hexOf (← IO.rand 0 (2^32 - 1)) 8
  return s

/-- Assign a request id: an incoming `X-Request-Id` is kept when `trust`
    and it is a short token, else a fresh one. Echoed in the response. -/
def requestId (trust : Bool := false) (header : String := "x-request-id") : NamedMiddleware :=
  ⟨"requestId", fun h req => do
    let incoming := (req.header? header).filter fun v =>
      trust && v.length ≤ 128 && !v.isEmpty && v.all fun c => c.isAlphanum || c == '-' || c == '_' || c == '.'
    let id ← match incoming with
      | some v => pure v
      | none => freshRequestId
    let res ← h (req.setLocal "request-id" id)
    pure (res.setHeader header id)⟩

/-- One JSON line per request: id, method, target, status, bytes, duration.
    Logs only the target and route-independent metadata, never bodies,
    headers, or cookies. -/
def accessLog (log : String → IO Unit := IO.eprintln) : NamedMiddleware :=
  ⟨"accessLog", fun h req => do
    let t0 ← IO.monoNanosNow
    let res ← h req
    let t1 ← IO.monoNanosNow
    let j := Lean.Json.mkObj [
      ("event", .str "access"), ("request_id", .str req.requestId),
      ("method", .str (toString req.method)), ("target", .str req.target),
      ("status", Lean.Json.num res.status), ("bytes", Lean.Json.num res.body.size),
      ("ms", Lean.Json.num (((t1 - t0) / 1000000 : Nat) : Lean.JsonNumber)),
      ("client", match req.clientAddr with | some a => .str a | none => .null)]
    log j.compress
    pure res⟩

/-! ### CORS -/

inductive OriginPolicy where
  /-- `*`; incompatible with credentials (the spec forbids it). -/
  | any
  | list (origins : List String)
  | predicate (ok : String → Bool)

structure CorsConfig where
  origins : OriginPolicy := .list []
  methods : List Method := [.get, .head, .post, .put, .patch, .delete]
  allowHeaders : List String := ["content-type", "authorization", "if-match", "idempotency-key"]
  exposeHeaders : List String := ["etag", "location", "x-request-id"]
  credentials : Bool := false
  maxAge : Option Nat := some 600

def CorsConfig.allows (c : CorsConfig) (origin : String) : Bool :=
  match c.origins with
  | .any => !c.credentials
  | .list os => os.contains origin
  | .predicate p => p origin

/-- CORS. Preflights (`OPTIONS` with `Access-Control-Request-Method`) are
    answered here and never reach the app. Disallowed origins get no CORS
    headers (the browser then blocks the response). `origins := .any` with
    `credentials := true` is denied: echoing an arbitrary origin would expose
    cookie-authenticated responses. Allowlisted origins with credentials are
    echoed and add `Vary: Origin`. -/
def cors (c : CorsConfig) : NamedMiddleware :=
  ⟨"cors", fun h req => do
    match req.header? "origin" with
    | none => h req
    | some origin =>
      let allowed := c.allows origin
      let decorate (r : Res) : Res :=
        if !allowed then r else
        let echo := match c.origins with
          | .any => !c.credentials
          | _ => false
        let r := r.setHeader "access-control-allow-origin" (if echo then "*" else origin)
        let r := if echo then r else r.addHeader "vary" "Origin"
        let r := if c.credentials then r.setHeader "access-control-allow-credentials" "true" else r
        if c.exposeHeaders.isEmpty then r
        else r.setHeader "access-control-expose-headers" (", ".intercalate c.exposeHeaders)
      if req.method == .options && (req.header? "access-control-request-method").isSome then
        if !allowed then pure (Problem.make 403 (some "origin not allowed")).toRes else
        let r := decorate (Res.empty 204)
        let r := r.setHeader "access-control-allow-methods" (", ".intercalate (c.methods.map toString))
        let r := r.setHeader "access-control-allow-headers" (", ".intercalate c.allowHeaders)
        let r := match c.maxAge with
          | some a => r.setHeader "access-control-max-age" (toString a)
          | none => r
        pure r
      else
        return decorate (← h req)⟩

/-! ### Trusted proxies -/

/-- Parse `Forwarded: for=1.2.3.4;proto=https, for=...` (RFC 7239) into
    `(for, proto)` pairs, nearest proxy last. -/
def parseForwarded (v : String) : List (Option String × Option String) :=
  (v.splitOn ",").map fun elem =>
    let pairs := (elem.splitOn ";").filterMap fun p =>
      match (p.trimAscii.toString).splitOn "=" with
      | [k, val] => some (k.trimAscii.toString.toLower, (val.trimAscii.toString.replace "\"" ""))
      | _ => none
    (pairs.lookup "for", pairs.lookup "proto")

inductive ProxyHeaders where
  | xForwarded
  | forwarded

/-- Honour `Forwarded` / `X-Forwarded-For` / `X-Forwarded-Proto` only when
    the socket peer is one of `trusted` (addresses without port). Walks the
    chain from the nearest hop and stops at the first untrusted address:
    that is the client. Otherwise the headers are ignored and removed, so
    handlers cannot mistake spoofed values for facts. Select the header family
    your trusted proxy appends; a client-supplied `Forwarded` must not override
    the proxy's `X-Forwarded-For`. -/
def trustedProxy (trusted : List String) (source : ProxyHeaders := .xForwarded) : NamedMiddleware :=
  ⟨"trustedProxy", fun h req => do
    let hostOf (a : String) : String :=
      if a.startsWith "[" then ((a.drop 1).takeWhile (· != ']')).toString
      else match a.splitOn ":" with
        | [host, _] => host
        | _ => a
    let peer := req.remoteAddr.map hostOf
    let strip (r : Req) : Req :=
      { r with headers := r.headers.filter fun (k, _) =>
          k != "forwarded" && k != "x-forwarded-for" && k != "x-forwarded-proto" && k != "x-forwarded-host" }
    match peer with
    | some p =>
      if !trusted.contains p then h (strip req) else
      let hops : List (Option String × Option String) :=
        match source with
        | .forwarded => (req.headerAll "forwarded").flatMap parseForwarded
        | .xForwarded =>
          let fors := ((req.headerAll "x-forwarded-for").flatMap (·.splitOn ",")).map (·.trimAscii.toString)
          let proto := ((req.headerAll "x-forwarded-proto").flatMap (·.splitOn ",")).getLast?.map (·.trimAscii.toString)
          fors.map fun f => (some f, proto)
      -- nearest hop last: walk from the end while hops are trusted proxies
      let rev := hops.reverse
      let client := (rev.find? fun (f, _) => match f with
        | some a => !trusted.contains (hostOf a)
        | none => false).bind (·.1) |>.map hostOf
      let proto := (rev.head?).bind (·.2)
      let r := strip req
      let r := match client with | some c => r.setLocal "client-addr" c | none => r
      let r := match proto with | some pr => r.setLocal "scheme" pr.toLower | none => r
      h r
    | none => h (strip req)⟩

/-! ### Timeouts -/

/-- Answer 504 if the inner app has not responded within `ms`. The inner
    task is cancelled (cooperatively: `IO.checkCanceled` in long loops).
    A handler that already committed state keeps its commit; the client
    sees 504 and must treat the outcome as unknown (use idempotency keys). -/
def timeout (ms : Nat) : NamedMiddleware :=
  ⟨s!"timeout({ms}ms)", fun h req => do
    let work ← IO.asTask (h req) .dedicated
    -- A libuv timer: waiting on it holds no thread (an `IO.sleep` task
    -- would pin a pool thread per in-flight request).
    let sleep ← Std.Async.Async.block (Std.Async.Sleep.mk (Std.Time.Millisecond.Offset.ofNat ms))
    let timer ← (sleep.wait).toIO
    let first ← IO.waitAny [work.map (fun r => some r), (show Task _ from timer).map (fun _ => none)]
    match first with
    | some (.ok res) => sleep.stop; pure res
    | some (.error e) => sleep.stop; throw e
    | none =>
      IO.cancel work
      pure ((Problem.make 504 (some "request timed out")).withExt "request_id" (.str req.requestId)).toRes⟩

/-! ### Health -/

/-- `GET /healthz` (liveness, always 200) and `GET /readyz` (readiness,
    503 when `ready` returns false, e.g. during shutdown or before the
    database is open). Answered before routing and authentication. -/
def health (ready : IO Bool := pure true) (live : String := "healthz") (readyPath : String := "readyz") :
    NamedMiddleware :=
  ⟨"health", fun h req => do
    if (req.method == .get || req.method == .head) && req.path == [live] then
      pure (Res.json (Lean.Json.mkObj [("status", .str "ok")]))
    else if (req.method == .get || req.method == .head) && req.path == [readyPath] then
      if ← ready then pure (Res.json (Lean.Json.mkObj [("status", .str "ready")]))
      else pure ((Problem.make 503 (some "not ready")).toRes)
    else h req⟩

/-- Add fixed response headers (security headers and similar). -/
def headers (hs : List (String × String)) (name : String := "headers") : NamedMiddleware :=
  ⟨name, fun h req => do
    let r ← h req
    pure (hs.foldl (fun r (k, v) => if (r.header? k).isSome then r else r.setHeader k v) r)⟩

/-- Conservative security headers for JSON APIs. -/
def securityHeaders : NamedMiddleware :=
  headers [("x-content-type-options", "nosniff"), ("referrer-policy", "no-referrer"),
           ("x-frame-options", "DENY"), ("content-security-policy", "default-src 'none'; frame-ancestors 'none'")]
    "securityHeaders"

end LeanApi
