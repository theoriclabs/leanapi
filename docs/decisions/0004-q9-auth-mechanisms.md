# 0004. LeanAPI provides auth mechanisms, apps own accounts (Q9, partial)

Status: accepted, M2, 2026-09-22.

## Decision

LeanAPI ships **mechanisms**:

| Mechanism | Module |
|---|---|
| `Authenticator` interface, `orElse`, `requireAuth`, `optionalAuth` | `LeanApi.Auth.Basic` |
| Bearer, Basic, session-cookie extraction over an app verifier | `LeanApi.Auth.Basic` |
| HS256 JWT verification with `exp`/`nbf`/`iat`/`iss`/`aud` and leeway; `alg: none` and other algorithms rejected before any signature work | `LeanApi.Auth.Jwt` |
| Opaque tokens: 256-bit random, stored and looked up only by SHA-256 digest | `LeanApi.Auth.Tokens` |
| scrypt password hashing; Basic over stored hashes, with dummy verification for unknown users | `LeanApi.Auth.Tokens` |

LeanAPI does **not** ship a user table, a session table, roles, tenants,
password reset, MFA, or login routes. These belong to the app's own domain,
where their invariants can be stated (e.g. the private-games example stores
players and token digests in its own LeanDB tables).

## Consequences

- Revocation of opaque tokens is a row delete in the app's table. JWTs are
  revoked only by expiry, or by an app `toActor` check against current state
  (a session generation or a deny list).
- An accepted JWT establishes what decision 0003 says and nothing more:
  current membership is re-checked by the domain at its commit point.
