import TestsNative.RouteChecks

-- The session table is private storage: it has no wire codec and is never published.
#synth Ontology.Wire RouteChecks.app.Session
