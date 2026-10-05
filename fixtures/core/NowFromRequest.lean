import TestsCore.PostPart1
open LeanDb.Model LeanApi.Core
-- The time must come from the server's clock; `Now` has no request codec.
def hostAt (me : SignedIn) (now : Now) : Op HostError Unit := pure ()
derive_operation hostAt
