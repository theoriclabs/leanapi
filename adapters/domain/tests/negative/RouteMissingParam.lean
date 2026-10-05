import RouteChecks

-- `rsvp`'s input field is `party`; the path names `:id`. Elaboration must name both.
def missing := route_binding% post "/parties/:id/rsvp" RouteChecks.rsvp
