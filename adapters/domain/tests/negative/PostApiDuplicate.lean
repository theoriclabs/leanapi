import tests.domain.PostPart1
import LeanApiDomain.App

-- An operation has one route: listing `rsvp` both explicitly and through `api := api` fails
-- at the `api` clause, naming the operation.
cascade% Rsvp.party

auth% account : Person using emailPassword(email)

app% PostApiApp where
  authentication := account
  routes := [post "/rsvp" rsvp.operation]
  pages := []
  api := api
