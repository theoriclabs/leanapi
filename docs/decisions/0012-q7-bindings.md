# 0012. Binding operations to routes (Q7, first answer)

Status: accepted (provisional), M5, 2026-09-22.

## Decision

A proved operation is bound explicitly, in ordinary Lean definitions:

| Part | Where (private-games) |
|---|---|
| Route table `Op × Method × template` | `App.routeTable` |
| Inputs from path, query, headers, body; `If-Match` → expected revision; `Idempotency-Key` | `App.decode` (pure), using M1 extractors and smart constructors |
| Authenticator | `App.authDigest` (bearer → token digest) plus the session table |
| What to load | `Input.need` |
| Decision and error → status mapping | `App.decideCore`, `App.domainRes` |
| Public projection of results | `App.gameJson`, `App.gameRes` (the `ETag` is the revision) |
| Retry identity | `Input.keyed` |

The native service (`App.operation`) and the model (`Model.operate`) both
consume the same parts. There is no DSL. Deriving these parts, generating
OpenAPI from them, and lifting the proofs into reusable lemmas are M7 work.

**Existence privacy (part of Q4):** the default is that "exists but not
visible" and "does not exist" give the same `404` (`App.hidden`), for reads
and for every command. A route that wants to reveal existence would map
`notParticipant` to 403 instead. No route in this slice does.
