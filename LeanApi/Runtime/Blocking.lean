/-
  Blocking work on dedicated threads behind a bounded queue (DESIGN §5.2).

  A `Worker` owns one OS thread that runs submitted jobs in order. Use one
  for a SQLite writer (single-writer discipline), or a `Pool` of them for
  read-only connections. `submit` fails fast with `.busy` when `capacity`
  jobs are already waiting: backpressure instead of unbounded queues.
-/
import Std.Sync

namespace LeanApi

inductive SubmitError where
  | busy
  | stopped
  deriving Repr, BEq

instance : ToString SubmitError := ⟨fun | .busy => "work queue full" | .stopped => "worker stopped"⟩

private structure Job where
  run : IO Unit

structure Worker where
  private queue : Std.CloseableChannel Job
  private pending : IO.Ref Nat
  capacity : Nat
  private thread : Task (Except IO.Error Unit)

namespace Worker

partial def start (capacity : Nat := 256) : IO Worker := do
  let queue ← Std.CloseableChannel.new (α := Job)
  let pending ← IO.mkRef 0
  let sync := queue.sync
  let rec loop : IO Unit := do
    match ← sync.recv with
    | none => pure ()
    | some job =>
      pending.modify (· - 1)
      try job.run catch _ => pure ()
      loop
  let thread ← IO.asTask loop .dedicated
  return { queue, pending, capacity, thread }

/-- Run `act` on the worker thread and wait for its result. -/
def run (w : Worker) (act : IO α) : IO (Except SubmitError α) := do
  let n ← w.pending.modifyGet fun n => (n, n + 1)
  if n ≥ w.capacity then
    w.pending.modify (· - 1)
    return .error .busy
  let promise ← IO.Promise.new (α := Except IO.Error α)
  let job : Job := ⟨do
    let r ← act.toBaseIO
    promise.resolve r⟩
  match ← (w.queue.sync.send job).toBaseIO with
  | .error _ =>
    w.pending.modify (· - 1)
    return .error .stopped
  | .ok () =>
    match ← IO.wait promise.result! with
    | .ok a => return .ok a
    | .error e => throw e

/-- `run`, throwing on backpressure. -/
def run! (w : Worker) (act : IO α) : IO α := do
  match ← w.run act with
  | .ok a => pure a
  | .error e => throw (IO.userError (toString e))

def stop (w : Worker) : IO Unit := do
  try w.queue.close catch _ => pure ()
  let _ ← IO.wait w.thread

end Worker

/-- A fixed set of workers; jobs go round-robin. -/
structure Pool where
  workers : Array Worker
  next : IO.Ref Nat

def Pool.start (n : Nat) (capacity : Nat := 256) : IO Pool := do
  let ws ← (List.range (max n 1)).toArray.mapM fun _ => Worker.start capacity
  return { workers := ws, next := ← IO.mkRef 0 }

def Pool.run (p : Pool) (act : IO α) : IO (Except SubmitError α) := do
  let i ← p.next.modifyGet fun i => (i, i + 1)
  match p.workers[i % p.workers.size]? with
  | some w => w.run act
  | none => return .error .stopped

def Pool.stop (p : Pool) : IO Unit := p.workers.forM Worker.stop

end LeanApi
