import LeanApi.Core

/-! `LeanApi.Core` is portable: its import closure is itself, `LeanApi.Publication`,
`LeanContract`, `LeanDb.Model`, `LeanOntology` and Lean's own libraries. No socket, SQLite,
native LeanDB or LeanAPI server module may appear in it, and no LeanReact, LeanJS or LeanApp
module at all. -/

open Lean in
run_cmd do
  let modules := (← getEnv).header.moduleNames
  let allowed (m : Name) : Bool :=
    [`LeanApi.Core, `LeanApi.Publication, `LeanContract, `LeanDb.Model, `LeanOntology, `Lean, `Init, `Std].any
      fun root => root == m || root.isPrefixOf m
  let foreign := modules.filter (!allowed ·)
  unless foreign.isEmpty do throwError "LeanApi.Core is not portable; its closure imports {foreign}"
  logInfo m!"LeanApi.Core closure: {modules.size} modules, all portable"
