# 0013. Typed middleware stages (Q8, second form)

Status: accepted (provisional), M7, 2026-09-22. Refines decision 0001.

## Decision

Two restricted middleware forms can enter theorems instead of being assumed
(`LeanApi/Http/Typed.lean`):

| Form | May observe | May do | Proved |
|---|---|---|---|
| `Stage.guard name observes decide` | Only the declared request parts (`Req.restrict`) | Refuse with a response computed from those parts, or pass the request through unchanged | `guard_transparent` (passing = inner app sees the exact request), `guard_observes` (refusal depends only on declared parts) |
| `Stage.decorate name observes headers` | Only the declared request parts | Add response headers | `decorate_preserves` (status and body are the inner app's) |

Consequences for claims: a stack made only of typed stages preserves a
route's proved status/body behaviour, except for guard refusals, which are
functions of the declared observation. An isolation claim therefore survives
if no guard observes hidden data (guards see only the request, never the
world).

Arbitrary `App → App` middleware (0001) remains available and remains
**assumed**. `recover`, `requestId`, `accessLog`, `timeout`, `cors` and
`trustedProxy` are still plain middleware: they need IO, state or response
rewriting beyond the typed forms. `securityHeaders` and a JSON media-type guard
have typed versions.
