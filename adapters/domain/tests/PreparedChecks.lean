import ContractFixture
import LeanApiDomain.Prepared
import Tests.TransactionClock

def main : IO UInt32 := do
  NativeFixture.run LeanApi.Domain.executePrepared
  let (_, result) ← (Tests.TransactionClock.run LeanApi.Domain.executePrepared).run {}
  IO.println s!"Prepared runner: {result.passed} passed, {result.failed.length} failed"
  pure (if result.failed.isEmpty then 0 else 1)
