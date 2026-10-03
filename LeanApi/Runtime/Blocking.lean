/-
  Blocking work off the async threads (DESIGN §5.2).

  A `Worker` owns one OS thread that runs submitted jobs in order. Use one
  for a SQLite writer (single-writer discipline), or a `Pool` of them for
  read-only connections. `submit` fails fast with `.busy` when `capacity`
  jobs are already waiting: backpressure instead of unbounded queues.

  `spawnBlocking` runs a job on a process-wide set of reusable `Threads`:
  the server runs each request's app there, and `timeout` its inner app.
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
  private begun : IO.Ref Nat
  capacity : Nat
  private thread : Task (Except IO.Error Unit)

namespace Worker

/-- Waiting jobs, excluding the active callback. Observation only; useful for
deterministic admission tests and queue instrumentation. -/
def queued (w : Worker) : IO Nat := w.pending.get

/-- Number of callbacks admitted to the worker, including the active callback. -/
def startedJobs (w : Worker) : IO Nat := w.begun.get

partial def start (capacity : Nat := 256) : IO Worker := do
  let queue ← Std.CloseableChannel.new (α := Job)
  let pending ← IO.mkRef 0
  let begun ← IO.mkRef 0
  let sync := queue.sync
  let rec loop : IO Unit := do
    match ← sync.recv with
    | none => pure ()
    | some job =>
      pending.modify (· - 1)
      begun.modify (· + 1)
      try job.run catch _ => pure ()
      loop
  let thread ← IO.asTask loop .dedicated
  return { queue, pending, begun, capacity, thread }

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

/-! ## Reusable threads -/

/-- Where an idle thread waits for its next job. A native mutex and
    condition variable: waiting on a `Task` instead would wake every idle
    thread each time any task in the program finishes. -/
private structure Mailbox where
  /-- `some (some job)`: run `job`; `some none`: exit; `none`: nothing yet. -/
  next : Std.Mutex (Option (Option (BaseIO Unit)))
  ready : Std.Condvar
  deriving Nonempty

namespace Mailbox

private def new : BaseIO Mailbox :=
  return { next := ← Std.Mutex.new none, ready := ← Std.Condvar.new }

private def put (m : Mailbox) (v : Option (BaseIO Unit)) : BaseIO Unit := do
  m.next.atomically (set (some v))
  m.ready.notifyOne

/-- Wait for the next job; `none` means exit. -/
private def take (m : Mailbox) : BaseIO (Option (BaseIO Unit)) :=
  m.next.atomicallyOnce m.ready (return (← get).isSome) do
    let v ← get
    set (none : Option (Option (BaseIO Unit)))
    return v.join

end Mailbox

private structure Idle where
  box : Mailbox
  since : Nat
  deriving Nonempty

private structure ThreadsState where
  /-- Oldest first. -/
  idle : Array Idle := #[]
  /-- A reaper thread is running; always so while `idle` is non-empty. -/
  reaping : Bool := false
  deriving Nonempty

/-- Threads for blocking jobs, reused between jobs (as Tokio's
    `spawn_blocking`). A job runs on an idle thread, or on a new one when
    none is idle, so it never waits behind another job: the concurrency of
    a dedicated thread per job, without starting a thread per job.

    A thread idle for over `keepAliveMs` exits. The runtime waits for every
    dedicated thread before the program exits, so a program that used these
    exits up to `keepAliveMs` late, or at once after `releaseIdle`. -/
structure Threads where
  private state : Std.Mutex ThreadsState
  keepAliveMs : Nat
  deriving Nonempty

namespace Threads

def new (keepAliveMs : Nat := 1000) : BaseIO Threads := do
  return { state := ← Std.Mutex.new {}, keepAliveMs }

/-- End the threads idle for over `keepAliveMs`, checking at most every
    100 ms, until none is idle. -/
private def reap (t : Threads) : BaseIO Unit := do
  let tick := max 1 (min 100 t.keepAliveMs)
  repeat
    IO.sleep tick.toUInt32
    let now ← IO.monoMsNow
    let (expired, done) ← t.state.atomically do
      let s ← get
      let n := (s.idle.toList.takeWhile (now - ·.since > t.keepAliveMs)).length
      let idle := s.idle.extract n s.idle.size
      set ({ idle, reaping := !idle.isEmpty } : ThreadsState)
      return (s.idle.extract 0 n, idle.isEmpty)
    for e in expired do e.box.put none
    if done then break

/-- Run `job`, then wait idle for the next one. The most recently idle
    thread is reused first, so surplus threads age out. -/
private def work (t : Threads) (first : BaseIO Unit) : BaseIO Unit := do
  let box ← Mailbox.new
  let mut job := first
  repeat
    job
    let startReaper ← t.state.atomically do
      let s ← get
      set { s with idle := s.idle.push { box, since := ← IO.monoMsNow }, reaping := true }
      return !s.reaping
    if startReaper then discard <| IO.asTask (reap t) .dedicated
    match ← box.take with
    | some next => job := next
    | none => break

/-- Run `act` on a pooled thread. The task holds its outcome. -/
def spawn (t : Threads) (act : IO α) : BaseIO (Task (Except IO.Error α)) := do
  let done ← IO.Promise.new
  let job : BaseIO Unit := do done.resolve (← act.toBaseIO)
  let reuse ← t.state.atomically do
    let s ← get
    set { s with idle := s.idle.pop }
    return s.idle.back?
  match reuse with
  | some w => w.box.put (some job)
  | none => discard <| IO.asTask (work t job) .dedicated
  return done.result?.map fun
    | some r => r
    | none => .error (.userError "blocking job was dropped")

/-- End every idle thread now, so that the program can exit at once. -/
def releaseIdle (t : Threads) : BaseIO Unit := do
  let idle ← t.state.atomically do
    let s ← get
    set { s with idle := #[] }
    return s.idle
  for i in idle do i.box.put none

/-- Threads waiting for a job. -/
def idleCount (t : Threads) : BaseIO Nat := t.state.atomically (return (← get).idle.size)

end Threads

/-- The threads behind `spawnBlocking`. -/
initialize blockingThreads : Threads ← Threads.new

/-- Run blocking `IO` (SQLite, FFI, CPU-heavy work) on a reused thread
    that no async task shares. -/
def spawnBlocking (act : IO α) : BaseIO (Task (Except IO.Error α)) :=
  blockingThreads.spawn act

end LeanApi
