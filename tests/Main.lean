import Tests.Http
import Tests.Middleware
import Tests.Notes
import Tests.Auth
import Tests.Games

open LeanApi.Test

def main : IO UInt32 := do
  let ((), r) ← (do
    Tests.Http.run
    Tests.Middleware.run
    Tests.Notes.run
    Tests.Auth.run
    Tests.Games.run
    : TestM Unit).run {}
  IO.println s!"\n{r.passed} passed, {r.failed.length} failed"
  return if r.failed.isEmpty then 0 else 1
