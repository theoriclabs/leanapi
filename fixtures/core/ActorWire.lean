import TestsCore.PostPart1
open LeanDb.Model LeanApi.Core
-- The actor is never request input or output: the app's `SignedIn` has no wire codec.
#synth Ontology.Wire SignedIn
