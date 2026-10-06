import TestsCore.PostPart1Run
import TestsCore.LoansRun
import TestsCore.ContractsRun
import TestsCore.Envelope

/-! `leanapi_core_tests`: the `LeanApi.Core` checks that run. The compile-time checks
(`#guard`, `#guard_msgs`) ran when these modules were built. -/

def main : IO Unit := do
  ContractsRun.main
  EnvelopeChecks.main
  PostPart1Run.main
  LoansRun.main
  IO.println "PASS leanapi_core_tests"
