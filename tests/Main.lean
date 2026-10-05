import LeanApiTests.Http
import LeanApiTests.Middleware
import LeanApiTests.Notes
import LeanApiTests.Auth
import LeanApiTests.Games
import LeanApiTests.Differential
import LeanApiTests.Tier2
import LeanApiTests.Props
import LeanApiTests.PropsCommands
import LeanApiTests.Registry
import LeanApiTests.Endpoint
import LeanApiTests.TransactionClock
import LeanApiTests.DbEndpoint
import LeanApiTests.Idempotency
import LeanApiTests.Helpdesk
import LeanApiTests.Billing
import LeanApiTests.Scheduling

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
    Tests.TransactionClock.run
    Tests.DbEndpoint.run
    Tests.Idempotency.run
    Tests.HelpdeskHttp.run
    Tests.Billing.run
    Tests.Schedule.run
    : TestM Unit).run {}
  IO.println s!"\n{r.passed} passed, {r.failed.length} failed"
  return if r.failed.isEmpty then 0 else 1
