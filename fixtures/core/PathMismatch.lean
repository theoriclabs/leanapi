import TestsCore.PostPart1
open LeanDb.Model LeanApi.Core
def misnamed : Api := [
  post "/parties/:partyId/rsvp" rsvp
]
