# 0014. What 1.0 means (Q12, revisited)

Status: proposed, M7, 2026-09-22.

## Where 0.5 stands

| Area | 0.5 | Needed for 1.0 |
|---|---|---|
| Routing, extraction, errors, middleware, auth | Done (0.1, 0.2) | Stability promise on these APIs |
| Conditional requests, rate limiting, SSE (buffered), tracing, multipart (buffered), security headers, OpenAPI + docs page | Done (0.5) | Streaming SSE and streaming multipart; OpenAPI schemas derived from decoders rather than declared |
| JWT | HS256 | RS256/ES256 and JWKS, which need leancrypto 0.2 |
| Proofs | Reusable `ScopedApp` isolation theorem; two apps (private-games, notes-with-sharing) discharge only domain obligations; typed middleware stages | A reusable idempotence theorem (today it is private-games-specific); trace noninterference across request sequences |
| Native ≡ model | Differential tests | Either a proof for the shell, or a documented, generated differential harness for every app |
| Coverage | `Router.coverage` report; tests fail on undeclared unproved routes | A `lake` script that fails the build |

## Proposed 1.0 criteria

1. **API stability** for `LeanApi.Http.*`, `LeanApi.Auth.*` and `LeanApi.Runtime.*`,
   with semver from then on.
2. **One reusable theorem per motivating guarantee**, isolation and keyed
   idempotence, each stated over `ScopedApp` and instantiated by at least two
   apps.
3. **Coverage enforced at build time**, plus an `EVIDENCE.md` generated from
   the audit list and the coverage report rather than written by hand.
4. **Production checklist**: TLS termination guidance, streaming bodies,
   receipt expiry (with the weakened theorem), metrics, and a load test in CI.

Not required for 1.0: HTTP/2, WebSockets on the HTTP port, event-sourced
storage, concurrency in the model.
