import TestsCore.PostPart1
open LeanDb.Model LeanApi.Core
def sneaky (me : SignedIn) (title : Title) (description : Text) (date : Time) : ReadOp Empty (Ref Party) := do
  Party.insert { host := me.id, title, description, date, guestList := .everyone }
