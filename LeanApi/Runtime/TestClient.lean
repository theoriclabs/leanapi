/-
  In-process test transport. Requests go through the real `Std.Http`
  parser and writer via `serveConnection` over a mock transport: no socket,
  but the same framing, limits, HEAD handling, and header validation as
  production. Every test in this repo goes through here.
-/
import LeanApi.Runtime.Server

namespace LeanApi.Test

open Std Std.Http Std.Http.Internal Std.Async

/-- A parsed HTTP/1.1 response. -/
structure Reply where
  status : Nat
  headers : List (String × String)
  body : String
  raw : String
  deriving Repr, Inhabited

def Reply.header? (r : Reply) (name : String) : Option String :=
  (r.headers.find? (·.1 == name.toLower)).map (·.2)

def Reply.json? (r : Reply) : Option Lean.Json := (Lean.Json.parse r.body).toOption

/-- Parse one response from raw bytes (status line, headers, body by
    `Content-Length`). -/
def parseReply (raw : String) : Reply :=
  let (head, body) := match raw.splitOn "\r\n\r\n" with
    | h :: rest => (h, "\r\n\r\n".intercalate rest)
    | [] => ("", "")
  let lines := head.splitOn "\r\n"
  let status := ((lines.headD "").splitOn " ").getD 1 "0" |>.toNat? |>.getD 0
  let headers := (lines.drop 1).filterMap fun l =>
    match l.splitOn ":" with
    | k :: vs@(_ :: _) => some (k.toLower, (":".intercalate vs).trimAscii.toString)
    | _ => none
  { status, headers, body, raw }

/-- Send raw bytes through a fresh connection and collect everything the
    server writes until it closes. The request should say `Connection: close`
    (the `request` helper does). -/
def sendRaw (svc : Service) (raw : ByteArray) (remote : Option Net.SocketAddress := none) : IO String := do
  let (client, server) ← Mock.new
  let exts := match remote with
    | some a => Extensions.empty.insert (Std.Http.Server.RemoteAddr.mk a)
    | none => Extensions.empty
  let handler := Std.Http.Server.Handler.ofFn (svc.handler (fun _ => pure ()))
  let out ← Async.block do
    client.send raw
    client.getSendChan.close
    Std.Http.Server.serveConnection server handler { lingeringTimeout := 1000, generateDate := false } exts |>.run
    let mut acc := ByteArray.empty
    repeat
      match ← client.tryRecv? with
      | some b => acc := acc ++ b
      | none => break
    return acc
  return String.fromUTF8? out |>.getD ""

/-- A structured request. -/
def request (svc : Service) (method : String) (target : String)
    (headers : List (String × String) := []) (body : String := "")
    (remote : Option Net.SocketAddress := none) : IO Reply := do
  let hs := headers.foldl (fun acc (k, v) => acc ++ s!"{k}: {v}\r\n") ""
  let len := if body.isEmpty && (method == "GET" || method == "HEAD" || method == "OPTIONS" || method == "DELETE")
    then "" else s!"Content-Length: {body.toUTF8.size}\r\n"
  let raw := s!"{method} {target} HTTP/1.1\r\nHost: test\r\nConnection: close\r\n{hs}{len}\r\n{body}"
  return parseReply (← sendRaw svc raw.toUTF8 remote)

def get (svc : Service) (target : String) (headers : List (String × String) := []) : IO Reply :=
  request svc "GET" target headers

def postJson (svc : Service) (target : String) (body : Lean.Json) (headers : List (String × String) := []) : IO Reply :=
  request svc "POST" target (("Content-Type", "application/json") :: headers) body.compress

/-! ## Tiny assertion harness -/

structure Results where
  passed : Nat := 0
  failed : List String := []

abbrev TestM := StateT Results IO

def check (name : String) (ok : Bool) (detail : String := "") : TestM Unit := do
  if ok then modify fun r => { r with passed := r.passed + 1 }
  else
    IO.eprintln s!"  FAIL {name}{if detail.isEmpty then "" else ": " ++ detail}"
    modify fun r => { r with failed := r.failed ++ [name] }

def checkEq [BEq α] [Repr α] (name : String) (got want : α) : TestM Unit :=
  check name (got == want) s!"got {repr got}, want {repr want}"

def section_ (name : String) (t : TestM Unit) : TestM Unit := do
  IO.println s!"• {name}"
  try t catch e => check s!"{name} (exception)" false (toString e)

end LeanApi.Test
