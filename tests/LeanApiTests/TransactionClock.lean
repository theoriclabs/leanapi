import LeanApi

namespace Tests.TransactionClock
open LeanApi LeanDb LeanApi.Test

structure Entry where
  name : String
  deriving LeanDb.Entity
schema% ClockDb := Entry

inductive CutoffError where
  | cutoff

instance : ToProblem CutoffError where
  status _ := ⟨409, by decide⟩

private def earlyOnly (now : Now) : LeanApi.Tx ClockDb CutoffError NoContent := do
  if now.val ≥ 100 then Txn.throw .cutoff
  discard <| Txn.insertNew (α := Entry) (Checked.of (Entry.mk "admitted") (by first | trivial | exact ⟨rfl, trivial⟩))
  pure ⟨⟩

def run (execute : DbProg.EnvExecutor ClockDb := DbProg.execWithEnv) : TestM Unit := do
  section_ "transaction clock after admission" do
    let tag ← Tokens.generate
    let path : System.FilePath := s!".lake/test-db/clock-{tag}.sqlite"
    IO.FS.createDirAll ".lake/test-db"
    let dc ← DbConns.open path (IsSchema.specs ClockDb) 1
    try
      let now ← IO.mkRef 99
      let samples ← IO.mkRef 0
      let fresh : IO Env := do
        samples.modify (· + 1)
        unless (← dc.writer.conn.txDepth.get) > 0 do
          throw (IO.userError "clock sampled outside transaction")
        return { now := ← now.get }
      let route := (DbEndpoint.post (s := ClockDb) "/early" earlyOnly).toRouteWithEnv dc fresh
        (fun _ => pure ()) execute
      let entered ← IO.Promise.new (α := Unit)
      let release ← IO.Promise.new (α := Unit)
      let held ← IO.asTask (dc.writer.run <| LeanDb.withTransaction do
        entered.resolve ()
        discard <| IO.wait release.result!) .dedicated
      discard <| IO.wait entered.result!
      let callStarted ← IO.Promise.new (α := Unit)
      let queued ← IO.asTask (do
        callStarted.resolve ()
        route.handler { method := .post }) .dedicated
      discard <| IO.wait callStarted.result!
      let mut waiting := false
      for _ in [:1000] do
        if (← dc.writer.worker.queued) == 1 then
          waiting := true
          break
        IO.sleep 1
      check "request actually queued before cutoff" waiting
      -- Advance the injected decision clock while the writer is certainly held.
      now.set 100
      checkEq "clock not sampled on queue entry" (← samples.get) 0
      release.resolve ()
      discard <| IO.wait held
      let response ← IO.ofExcept (← IO.wait queued)
      checkEq "queued before cutoff, admitted at cutoff: rejected" response.status 409
      checkEq "one transaction clock sample" (← samples.get) 1
      let count ← DbM.run dc.writer.conn (Read.run (Read.count (Query.from Entry (s := ClockDb))))
      checkEq "failed guard inserts no row" (count.toOption.bind (·.toOption)) (some 0)
      now.set 99
      checkEq "strictly before cutoff succeeds" (← route.handler { method := .post }).status 204
      let count ← DbM.run dc.writer.conn (Read.run (Read.count (Query.from Entry (s := ClockDb))))
      checkEq "success actually persisted" (count.toOption.bind (·.toOption)) (some 1)

      -- A second SQLite connection holds the engine writer lock, while our
      -- process worker is free. Sampling merely after the queue would fail this.
      let .ok external ← openDbRaw path | throw (IO.userError "external writer")
      let locked ← IO.Promise.new (α := Unit)
      let unlock ← IO.Promise.new (α := Unit)
      let externalTask ← IO.asTask (DbM.run external <| LeanDb.withTransaction do
        locked.resolve ()
        discard <| IO.wait unlock.result!) .dedicated
      discard <| IO.wait locked.result!
      now.set 99
      let samplesBefore ← samples.get
      let startedBefore ← dc.writer.worker.startedJobs
      let blocked ← IO.asTask (route.handler { method := .post }) .dedicated
      let mut admitted := false
      for _ in [:1000] do
        if (← dc.writer.worker.startedJobs) > startedBefore then
          admitted := true
          break
        IO.sleep 1
      check "process worker admitted request under external lock" admitted
      checkEq "SQLite writer lock acquired before clock sample" (← samples.get) samplesBefore
      now.set 100
      unlock.resolve ()
      discard <| IO.wait externalTask
      let response ← IO.ofExcept (← IO.wait blocked)
      checkEq "external-lock delayed command rejected at cutoff" response.status 409
      let count ← DbM.run dc.writer.conn (Read.run (Read.count (Query.from Entry (s := ClockDb))))
      checkEq "external-lock refusal leaves prior row unchanged" (count.toOption.bind (·.toOption)) (some 1)
    finally dc.close
end Tests.TransactionClock
