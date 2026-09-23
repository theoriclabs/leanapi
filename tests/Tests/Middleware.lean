import LeanApi

namespace Tests.Middleware

open LeanApi LeanApi.Test Lean

def echoClient : App := fun r =>
  pure (Res.text s!"client={r.clientAddr.getD "-"} scheme={(r.local? "scheme").getD "-"} xff={(r.header? "x-forwarded-for").getD "-"}")

def users : List (String × String × String) := [("tok-alice", "alice", "pw-a"), ("tok-bob", "bob", "pw-b")]

def bearerAuth : Authenticator String := bearer fun t => pure ((users.find? (·.1 == t)).map (·.2.1))
def basicAuth : Authenticator String := basic fun u p => pure ((users.find? fun (_, n, pw) => n == u && pw == p).map (·.2.1))
def either := bearerAuth.orElse basicAuth

def routes : List Route := [
  Route.get "/client" echoClient,
  Route.get "/me" (requireAuth either fun who _ => pure (Res.text who)),
  Route.get "/maybe" (optionalAuth bearerAuth fun who _ => pure (Res.text (who.getD "anon"))),
  Route.get "/slow" fun _ => do IO.sleep 300; pure (Res.text "late"),
  Route.get "/id" fun r => pure (Res.text r.requestId)
]

def stack : Stack := Stack.of [
  recover (fun _ => pure ()), requestId, health, securityHeaders,
  cors { origins := .list ["https://app.example"], credentials := true },
  trustedProxy ["10.0.0.1"], timeout 150]

def svc : Service := Service.ofRouter (Router.build! routes) stack

def peer (a : String) (port : UInt16 := 5555) : Option Std.Net.SocketAddress :=
  (Std.Net.IPv4Addr.ofString a).map fun ip => .v4 { addr := ip, port }

def run : TestM Unit := do
  section_ "middleware order" do
    checkEq "describe" stack.describe
      "recover → requestId → health → securityHeaders → cors → trustedProxy → timeout(150ms) → app"
    let log ← IO.mkRef ([] : List String)
    let tag (n : String) : NamedMiddleware := ⟨n, fun h r => do log.modify (· ++ [n ++ ">"]); let x ← h r; log.modify (· ++ ["<" ++ n]); pure x⟩
    let s := Stack.of [tag "a", tag "b"]
    let _ ← s.apply (fun _ => do log.modify (· ++ ["app"]); pure {}) default
    checkEq "onion order" (← log.get) ["a>", "b>", "app", "<b", "<a"]

  section_ "request id, health, security headers" do
    let r ← get svc "/id"
    check "request id header" ((r.header? "x-request-id").map (·.length) == some 32)
    checkEq "request id visible to handler" (some r.body) (r.header? "x-request-id")
    let r ← get svc "/id" [("X-Request-Id", "spoofed")]
    check "untrusted incoming id replaced" (r.header? "x-request-id" != some "spoofed")
    checkEq "healthz" (← get svc "/healthz").status 200
    checkEq "readyz" (← get svc "/readyz").status 200
    let notReady := Service.ofRouter (Router.build! routes) (Stack.of [health (pure false)])
    checkEq "readyz 503" (← get notReady "/readyz").status 503
    checkEq "nosniff" ((← get svc "/id").header? "x-content-type-options") (some "nosniff")

  section_ "CORS" do
    let r ← request svc "OPTIONS" "/me" [("Origin", "https://app.example"), ("Access-Control-Request-Method", "GET")]
    checkEq "preflight 204" r.status 204
    checkEq "preflight origin echoed" (r.header? "access-control-allow-origin") (some "https://app.example")
    checkEq "credentials" (r.header? "access-control-allow-credentials") (some "true")
    check "allow-methods" ((r.header? "access-control-allow-methods").isSome)
    let r ← request svc "OPTIONS" "/me" [("Origin", "https://evil.example"), ("Access-Control-Request-Method", "GET")]
    checkEq "preflight bad origin 403" r.status 403
    let r ← get svc "/id" [("Origin", "https://evil.example")]
    checkEq "simple bad origin: no ACAO" (r.header? "access-control-allow-origin") none
    let r ← get svc "/id" [("Origin", "https://app.example")]
    checkEq "simple good origin" (r.header? "access-control-allow-origin") (some "https://app.example")
    checkEq "vary origin" (r.header? "vary") (some "Origin")

  section_ "trusted proxies" do
    let r ← request svc "GET" "/client" [("X-Forwarded-For", "1.2.3.4"), ("X-Forwarded-Proto", "https")] "" (peer "10.0.0.1")
    checkEq "trusted peer: xff honoured" r.body "client=1.2.3.4 scheme=https xff=-"
    let r ← request svc "GET" "/client" [("X-Forwarded-For", "1.2.3.4")] "" (peer "8.8.8.8")
    checkEq "untrusted peer: xff stripped" r.body "client=8.8.8.8:5555 scheme=- xff=-"
    let r ← request svc "GET" "/client" [("Forwarded", "for=9.9.9.9;proto=http, for=10.0.0.1")] "" (peer "10.0.0.1")
    checkEq "Forwarded chain skips trusted hops" r.body "client=9.9.9.9 scheme=- xff=-"

  section_ "timeout" do
    let r ← get svc "/slow"
    checkEq "504 after timeout" r.status 504

  section_ "authentication" do
    checkEq "bearer ok" (← get svc "/me" [("Authorization", "Bearer tok-alice")]).body "alice"
    checkEq "bearer scheme case-insensitive" (← get svc "/me" [("Authorization", "bearer tok-bob")]).body "bob"
    let basicHdr := "Basic " ++ Base64.encode "bob:pw-b".toUTF8
    checkEq "basic ok" (← get svc "/me" [("Authorization", basicHdr)]).body "bob"
    let r ← get svc "/me"
    checkEq "missing 401" r.status 401
    checkEq "challenge lists both" (r.header? "www-authenticate") (some "Bearer realm=\"api\", Basic realm=\"api\", charset=\"UTF-8\"")
    checkEq "bad token 401" (← get svc "/me" [("Authorization", "Bearer nope")]).status 401
    checkEq "bad password 401" (← get svc "/me" [("Authorization", "Basic " ++ Base64.encode "bob:x".toUTF8)]).status 401
    checkEq "malformed basic 401" (← get svc "/me" [("Authorization", "Basic !!!")]).status 401
    checkEq "optional anon" (← get svc "/maybe").body "anon"
    checkEq "optional authed" (← get svc "/maybe" [("Authorization", "Bearer tok-alice")]).body "alice"
    checkEq "optional invalid still 401" (← get svc "/maybe" [("Authorization", "Bearer nope")]).status 401
    checkEq "password with colon" (basicCredentials? (Req.mk' .get "/" [("authorization", "Basic " ++ Base64.encode "u:a:b".toUTF8)])) (some ("u", "a:b"))

  section_ "blocking worker queue" do
    let w ← Worker.start 2
    checkEq "runs jobs" (← w.run (pure 41 : IO Nat)).toOption (some 41)
    let order ← IO.mkRef ([] : List Nat)
    let ts ← (List.range 20).mapM fun i => IO.asTask (w.run! (order.modify (· ++ [i])))
    for t in ts do let _ ← IO.wait t
    check "backpressure or completion" ((← order.get).length ≤ 20)
    w.stop
    let w ← Worker.start 1
    let gate ← IO.Promise.new (α := Unit)
    let blocker ← IO.asTask (w.run! (IO.wait gate.result!))
    IO.sleep 50
    let queued ← IO.asTask (w.run! (pure ()))
    IO.sleep 50
    checkEq "full queue is busy" (← w.run (pure ())).toOption none
    gate.resolve ()
    let _ ← IO.wait blocker
    let _ ← IO.wait queued
    w.stop

end Tests.Middleware
