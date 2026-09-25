/-
  Serve an API in one call, Express-style: `app.listen 3000`.
-/
import LeanApi.Http.Endpoint
import LeanApi.Runtime.Server

namespace LeanApi

/-- Serve an API whose handlers read and write `state` (kept in memory,
    under a mutex) on `port`, until Ctrl-C or SIGTERM; then stop accepting
    and let open requests finish. `stack` is the middleware, outermost first. -/
def Api.listenWith (api : Api σ) (state : σ) (port : Nat := 8080) (stack : Stack := {})
    (host : String := "127.0.0.1") : IO Unit := do
  let store := Store.ofMutex (← Std.Mutex.new state)
  serve (api.service store stack) { host, port := port.toUInt16 }
    (onReady := fun p => IO.eprintln s!"listening on http://{host}:{p}")

/-- Serve a stateless API on `port`: `app.listen 3000`. -/
def Api.listen (api : Api Unit) (port : Nat := 8080) (stack : Stack := {})
    (host : String := "127.0.0.1") : IO Unit :=
  api.listenWith () port stack host

end LeanApi
