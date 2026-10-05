import TestsNative.RouteChecks

-- GET is for query operations only; `rsvp` is a command.
def getCommand := route_binding% get "/parties/:party/rsvp" RouteChecks.rsvp.operation
