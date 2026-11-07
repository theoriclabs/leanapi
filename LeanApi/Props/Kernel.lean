import LeanApi.Props.Sys
import LeanApi.Props.Ops
import LeanApi.Props.Store
import LeanApi.Props.Registry
import LeanApi.Props.Authoring
import LeanApi.Props.Stored
import LeanApi.Props.Enumerate
import LeanApi.Props.Check
import LeanApi.Props.Shapes
import LeanApi.Props.Keyed

/-! # The property kernel, without the server

Every `LeanApi.Props` module except `Bridge` (`ScopedApp.toSys`, which needs the HTTP pipeline):
transition systems (`Sys`), invariants and their proof principles, the operator algebra,
stores, keyed systems, `invariant`/`preserves`/`invariant_cases`, `#check_invariant` and the
registry. Its import closure is itself and Lean's own libraries, without `Std.Http`
(`scripts/PropsClosure.lean`), so a client library such as LeanReact can state and prove
properties of its own state machines without depending on the server. It is built as the
`LeanProps` library; `import LeanApi.Props` still brings in everything, `Bridge` included. -/
