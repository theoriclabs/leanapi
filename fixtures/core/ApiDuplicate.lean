import TestsCore.PostPart1
open LeanDb.Model LeanApi.Core

-- An operation has one route.
def twice : Api := [
  post "/parties/:party/rsvp" rsvp,
  post "/parties/:party/going" rsvp
]
