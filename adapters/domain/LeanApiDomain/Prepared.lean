import LeanApiDomain.Contract
import LeanDb.Typed.Rollback

/-! Optional current-DB integration. The released core DB pin predates runPrepared;
this module is consumed only by a graph that provides the shared runner/laws. -/
namespace LeanApi.Domain
open LeanApi LeanDb

/-- The database owns transaction preparation; no API-owned outer/savepoint runner.
Use `app.service dc (execute := executePrepared)` after selecting the compatible DB. -/
def executePrepared {s : Type} [IsSchema s] : Published.Executor s
  | dc, fresh, .pure, program => read dc fresh program
  | dc, fresh, .reads, program => read dc fresh program
  | dc, fresh, .writes, program => do
    match ← dc.writer.run (Txn.runPrepared (s := s) (do fresh) (fun env => program env)) with
    | .error .busy => return .error (.locking "writer queue full")
    | .error .stopped => return .error (.io "writer stopped")
    | .ok (.error error) => return .error (DbFault.ofDbError error)
    | .ok (.ok (.error fault)) => return .error fault
    | .ok (.ok (.ok result)) => return .ok (DbProg.merge result)
where
  read (dc : DbConns) (fresh : IO Env) (program : Env → Read s Res) : IO (Except DbFault Res) := do
    match ← dc.read (Read.runPrepared (s := s) (do fresh) program) with
    | .error .busy => return .error (.locking "reader queue full")
    | .error .stopped => return .error (.io "reader stopped")
    | .ok (.error error) => return .error (DbFault.ofDbError error)
    | .ok (.ok result) => return result

/-- Carry-over uses the DB-owned rollback law of the actual native meaning. -/
theorem prepared_abort_restores {s Scope Error Output : Type} [IsSchema s]
    (program : Txn Scope s Error Output) (state : DbState s) (error : Error)
    (failed : (Txn.denote program state).1 = .error error) :
    (Txn.denote program state).2 = state :=
  Txn.denote_abort_restores program state error failed

end LeanApi.Domain
