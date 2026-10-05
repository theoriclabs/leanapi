import TestsNative.RouteChecks

-- A password has no path codec: it can never be bound from a URL.
def leaky := route_binding% post "/sign-in/:password" RouteChecks.signIn.operation
