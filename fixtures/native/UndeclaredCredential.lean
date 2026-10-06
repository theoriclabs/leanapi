import TestsNative.RouteChecks

-- `authentication := P with C` needs `C` declared with `credential C.profile C.hash`.
app% notACredential where
  authentication := RouteChecks.Person with RouteChecks.Party
  api := RouteChecks.api
