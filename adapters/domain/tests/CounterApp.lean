import LeanApiDomain.App
import LeanApp.Core
open LeanApp.Core

/-! Generality fixture for an app with no accounts: public named counters, served by
`app% Name where api := api`. No person, credential, session or page; every operation takes
no actor. The current domain sits at the root namespace, as a small app's would; `CounterV1`
is the first deployment, before counters had a `step`, so the migration runs on a real old
database. `scripts/ddd_counter_acceptance.mjs` serves both over real curl and SQLite. -/

namespace CounterV1

structure Counter where
  name  : Name
  count : Nat
  deriving Entity

constraint Counter.uniqueName : unique name

inductive CreateError where
  | nameTaken

def newCounter (name : Name) : Op CreateError (Ref Counter) := do
  match ← Counter.insert { name, count := 0 } with
  | .ok id => pure id
  | .error .uniqueName => throw .nameTaken

def api : Api := [
  post "/counters" newCounter
]

end CounterV1

/-! ## The current counters (root namespace) -/

structure Counter where
  name  : Name
  count : Nat
  step  : Nat
  deriving Entity

-- One counter per name; a second `newCounter` is the typed `nameTaken`.
constraint Counter.uniqueName : unique name

inductive CreateError where
  | nameTaken

inductive CounterError where
  | notFound

structure CounterView where
  name  : Name
  count : Nat
  step  : Nat

def newCounter (name : Name) (step : Nat) : Op CreateError (Ref Counter) := do
  match ← Counter.insert { name, count := 0, step } with
  | .ok id => pure id
  | .error .uniqueName => throw .nameTaken

def increment (counter : Ref Counter) : Op CounterError Nat := do
  let some c ← Counter.find counter | throw .notFound
  let count := c.count + c.step
  -- The name is unchanged, so the update cannot conflict.
  let _ ← Counter.update c { c.toCounter with count }
  pure count

def getCounter (counter : Ref Counter) : ReadOp CounterError CounterView := do
  let some c ← Counter.find counter | throw .notFound
  return { name := c.name, count := c.count, step := c.step }

def api : Api := [
  post "/counters"                    newCounter,
  get  "/counters/:counter"           getCounter,
  post "/counters/:counter/increment" increment
]

app% counterV1 where
  api := CounterV1.api

app% counters where
  api := api
  migrations := [
    -- Counters created before `step` existed counted by one.
    addStep := Counter.addField step (fill := 1)
  ]

def main (args : List String) : IO UInt32 := do
  let config : LeanApi.Domain.AppConfig := { database := "counters.sqlite" }
  match args with
  | "v1" :: rest => counterV1.main rest config
  | "v2" :: rest => counters.main rest config
  -- The current build as it would be before its migration was written.
  | "v2-unmigrated" :: rest => LeanApi.Domain.PublicApp.main { counters with migrations := [] } rest config
  | _ => do
    IO.eprintln "usage: domain_counter_app (v1 | v2 | v2-unmigrated) [migrate [--check]]"
    return 2
