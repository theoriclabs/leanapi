import TestsCore.PostPart1
open LeanDb.Model LeanApi.Core
-- Only the session layer builds an actor: the constructor is private.
def forged (id : Ref Person) : SignedIn := SignedIn.mk id
