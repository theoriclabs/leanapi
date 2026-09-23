/-
  The transport edge. The only module that touches `Std.Http` request and
  response types (risk mitigation: `Std.Http` may change between
  toolchains; it is kept behind this one module).

  Per request:
  1. Decode the head into a `Req` (method, decoded path, query, headers,
     peer address). Unsupported methods: 501. Undecodable paths: 400.
  2. Ask the router for the route's body limit and read the body while
     streaming, stopping with 413 as soon as the limit is exceeded
     (a `Content-Length` over the limit is refused before reading).
  3. Run the app on a dedicated thread (handlers do blocking `IO`: SQLite,
     FFI), so async pool threads are never pinned.
  4. Encode the `Res`.
-/
import Std.Http
import LeanApi.Http.Middleware

namespace LeanApi

open Std Std.Http Std.Async

/-- An application ready to serve: the app (router wrapped in middleware)
    plus the router, for per-route body limits. -/
structure Service where
  app : App
  /-- `some n`: read at most `n` bytes. `none`: do not read the body. -/
  bodyLimit : Req → Option Nat := fun _ => some (1024 * 1024)

def Service.ofRouter (r : Router) (stack : Stack := {}) : Service :=
  { app := stack.apply r.app, bodyLimit := r.bodyLimit }

/-- Decode a request head. `none` when the method is not routable. -/
def decodeHead (line : Request.Head) (remote : Option String) : Except Res Req := do
  let some m := Method.ofStd? line.method
    | throw (Problem.make 501 (some s!"method {line.method} is not supported")).toRes
  let pathObj := line.uri.path
  let rawSegs := pathObj.segments.toList.map toString
  let trailing := rawSegs.length > 1 && rawSegs.getLast? == some ""
  let rawSegs := if rawSegs == [""] then [] else if trailing then rawSegs.dropLast else rawSegs
  let some segs := rawSegs.mapM (fun s => Url.percentDecode s)
    | throw (Problem.badRequest "path is not valid percent-encoded UTF-8").toRes
  if segs.any (·.isEmpty) then
    throw (Problem.badRequest "empty path segment").toRes
  let query := line.uri.query.toArray.toList.filterMap fun (k, v) => do
    let k ← Url.percentDecode (toString k) true
    let v ← match v with
      | some e => Url.percentDecode (toString e) true
      | none => some ""
    return (k, v)
  let headers := line.headers.toList.map fun (k, v) => (k.value, v.value)
  return { method := m, path := segs, target := toString line.uri, trailingSlash := trailing,
           query, headers, remoteAddr := remote }

/-- Read at most `limit` bytes; `none` if the body is longer. -/
partial def readLimited (stream : Body.Stream) (limit : Nat) : ContextAsync (Option ByteArray) := do
  let rec loop (acc : ByteArray) : ContextAsync (Option ByteArray) := do
    match ← Body.Stream.NextChunk.nextChunk stream with
    | none => return some acc
    | some chunk =>
      if acc.size + chunk.data.size > limit then return none
      loop (acc ++ chunk.data)
  loop .empty

/-- Run blocking work on a dedicated OS thread and await it without
    occupying an async pool thread. -/
def runBlocking (act : IO α) : Async α := do
  let t ← IO.asTask act .dedicated
  match ← await t with
  | .ok a => pure a
  | .error e => throw e

/-- The `Std.Http` handler for a service. -/
def Service.handler (svc : Service) (log : String → IO Unit := IO.eprintln) :
    Request Body.Stream → ContextAsync (Response Body.Any) := fun request => do
  let remote := (request.extensions.get Server.RemoteAddr).map (toString ·.addr)
  let res ← match decodeHead request.line remote with
    | .error r => pure r
    | .ok req =>
      match svc.bodyLimit req with
      | none =>
        try runBlocking (svc.app req)
        catch _ => pure (Problem.make 500).toRes
      | some limit =>
      let declared ← request.body.getKnownSize
      let tooBig : Bool := match declared with
        | some (.fixed n) => decide (n > limit)
        | _ => false
      if tooBig then pure (Problem.make 413 (some s!"body exceeds {limit} bytes")).toRes else
      match ← readLimited request.body limit with
      | none => pure (Problem.make 413 (some s!"body exceeds {limit} bytes")).toRes
      | some body =>
        try runBlocking (svc.app { req with body })
        catch e => do
          log s!"\{\"event\":\"error\",\"error\":{Lean.Json.str (toString e) |>.compress}}"
          pure (Problem.make 500).toRes
  res.toStd

structure ServeConfig where
  host : String := "127.0.0.1"
  port : UInt16 := 8080
  http : Std.Http.Config := { generateDate := true }
  /-- Stop accepting and drain on SIGTERM / SIGINT. -/
  handleSignals : Bool := true
  log : String → IO Unit := IO.eprintln

/-- Serve until SIGTERM/SIGINT, then shut down gracefully: stop accepting,
    let active connections finish, return. `onReady` receives the bound port. -/
def serve (svc : Service) (cfg : ServeConfig := {}) (onReady : UInt16 → IO Unit := fun _ => pure ())
    (draining : Option (IO.Ref Bool) := none) : IO Unit := do
  let some ip := Net.IPv4Addr.ofString cfg.host
    | throw (IO.userError s!"invalid IPv4 host {cfg.host}")
  let addr : Net.SocketAddress := .v4 { addr := ip, port := cfg.port }
  let handler := Std.Http.Server.Handler.ofFn (svc.handler cfg.log)
  let server ← Async.block (Std.Http.Server.serve addr handler cfg.http)
  onReady cfg.port
  cfg.log (Lean.Json.mkObj [("event", .str "leanapi.ready"), ("host", .str cfg.host),
    ("port", Lean.Json.num cfg.port.toNat)]).compress
  if cfg.handleSignals then
    let term ← Signal.Waiter.mk .sigterm false
    let int ← Signal.Waiter.mk .sigint false
    let tt ← term.wait
    let ti ← int.wait
    let _ ← IO.waitAny [tt.map (fun _ => ()), ti.map (fun _ => ())]
    if let some d := draining then d.set true
    cfg.log "{\"event\":\"leanapi.draining\"}"
    Async.block server.shutdownAndWait
    cfg.log "{\"event\":\"leanapi.stopped\"}"
  else
    Async.block server.waitShutdown

end LeanApi
