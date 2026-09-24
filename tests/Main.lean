import Tests.Http
import Tests.Middleware
import Tests.Notes
import Tests.Auth
import Tests.Games
import Tests.Differential
import Tests.Tier2
import Tests.Props
import Tests.PropsCommands
import Tests.Registry
import Tests.Endpoint
import Tests.DbEndpoint
import Tests.Idempotency
import Tests.Helpdesk
import Tests.Billing

open LeanApi.Test

def main : IO UInt32 := do
  let ((), r) ← (do
    Tests.Http.run
    Tests.Middleware.run
    Tests.Notes.run
    Tests.Auth.run
    Tests.Games.run
    Tests.Differential.run
    Tests.Tier2.run
    Tests.Props.run
    Tests.Endpoint.run
    Tests.DbEndpoint.run
    Tests.Idempotency.run
    Tests.HelpdeskHttp.run
    Tests.Billing.run
    : TestM Unit).run {}
  IO.println s!"\n{r.passed} passed, {r.failed.length} failed"
  return if r.failed.isEmpty then 0 else 1
