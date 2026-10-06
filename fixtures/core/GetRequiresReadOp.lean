import TestsCore.PostPart1
open LeanDb.Model LeanApi.Core
def writable : Api := [
  get "/parties/:party/rsvp" rsvp
]
