import LeanApiDomain.App

namespace RouteAppEntry
open LeanApp.Domain

@[entity] structure Person where
  name : Name
  email : Email

unique% Person.byEmail := email

auth% account : Person using emailPassword(email)

command% rename (me : SignedIn Person) (name : Name) : Unit := do
  let row ← find Person me.id else personMissing
  change row {name}

end RouteAppEntry

-- An `app%` route whose parameter names no input field fails at that entry.
app% RouteAppEntry.app where
  authentication := RouteAppEntry.account
  routes := [
    post "/sign-up" RouteAppEntry.account.signUp,
    post "/people/:person/name" RouteAppEntry.rename
  ]
  pages := []
