import LeanApiDomain.Runtime

open LeanApi.Domain

private def check (value : Bool) (label : String) : IO Unit :=
  unless value do throw (IO.userError label)

def main : IO Unit := do
  let gate : KDFGate := {active := ← Std.Mutex.new 0}
  let enteredA ← IO.Promise.new (α := Unit)
  let enteredB ← IO.Promise.new (α := Unit)
  let release ← IO.Promise.new (α := Unit)
  let first ← IO.asTask (gate.run (E := Empty) (do
    enteredA.resolve (); discard <| IO.wait release.result!; pure 1)) .dedicated
  let second ← IO.asTask (gate.run (E := Empty) (do
    enteredB.resolve (); discard <| IO.wait release.result!; pure 2)) .dedicated
  discard <| IO.wait enteredA.result!
  discard <| IO.wait enteredB.result!
  let denied ← gate.run (E := Empty) (pure 3)
  check (match denied with | .error (.protocol fault) => fault.code == "auth.busy" && fault.status == some 503 | _ => false)
    "third concurrent preparation refuses with typed retryable framework failure"
  check ((← gate.active.atomically get) == 2) "concurrent preparation capacity remains two"
  release.resolve ()
  let a ← IO.ofExcept (← IO.wait first)
  let b ← IO.ofExcept (← IO.wait second)
  check (match a,b with | .ok 1,.ok 2 => true | _,_ => false) "admitted preparations finish"
  check ((← gate.active.atomically get) == 0) "successful preparations release all slots"
  let failed ← (gate.run (A := Unit) (E := Empty) (throw (IO.userError "fixture"))).toBaseIO
  check (match failed with | .error _ => true | _ => false) "preparation exception remains observable"
  check ((← gate.active.atomically get) == 0) "exception releases preparation slot"
  let next ← gate.run (E := Empty) (pure 4)
  check (match next with | .ok 4 => true | _ => false) "gate usable after exception"
  IO.println "PASS: synchronized KDF admission capacity and success/exception release"
