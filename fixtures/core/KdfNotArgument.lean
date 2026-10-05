import TestsCore.PostPart1
open LeanDb.Model LeanApi.Core
-- A KDF input must be one of the operation's own arguments.
def hashFixed (me : SignedIn) : Op Empty PasswordHash := do
  let fixed ← match Password.parse "a fixed password!" with
    | .ok p => pure p
    | .error _ => throw (nomatch ())
  fixed.hash
derive_operation hashFixed
