/-
  A service: the router wrapped in its middleware, plus the router's
  per-route body limits. Plain data, with no transport: `serve`
  (`LeanApi/Runtime/Server.lean`) runs one on a socket, and the test client
  calls one in process.
-/
import LeanApi.Http.Middleware

namespace LeanApi

/-- An application ready to serve: the app (router wrapped in middleware)
    plus the router, for per-route body limits. -/
structure Service where
  app : App
  /-- `some n`: read at most `n` bytes. `none`: do not read the body. -/
  bodyLimit : Req → Option Nat := fun _ => some (1024 * 1024)

def Service.ofRouter (r : Router) (stack : Stack := {}) : Service :=
  { app := stack.apply r.app, bodyLimit := r.bodyLimit }

end LeanApi
