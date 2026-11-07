import LeanApi.Props.Kernel

/-! The property kernel is server-free: its import closure is `LeanApi.Props` (without
`Bridge`) and the toolchain's own libraries (`Init`, `Std`, `Lean`, `Lake`), with no module of
any package (no LeanAPI server, HTTP pipeline, SQLite, LeanDB or crypto), so a client library
can depend on it without the server. -/

open Lean in
run_cmd do
  let modules := (← getEnv).header.moduleNames
  let allowed (m : Name) : Bool :=
    m != `LeanApi.Props.Bridge &&
    ([`LeanApi.Props, `Lean, `Init, `Std, `Lake].any fun root => root == m || root.isPrefixOf m)
  let foreign := modules.filter (!allowed ·)
  unless foreign.isEmpty do throwError "The property kernel is not server-free; its closure imports {foreign}"
  logInfo m!"LeanApi.Props.Kernel closure: {modules.size} modules, none from another package"
