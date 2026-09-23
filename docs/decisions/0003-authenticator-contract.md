# 0003. The authenticator contract

Status: accepted, M1, 2026-09-22. Part of Q9.

## Decision

`Authenticator actor` has a `challenge` (for `WWW-Authenticate`) and
`run : Req → IO (Except AuthFailure actor)`. `AuthFailure` is `missing`
(no credential of this scheme) or `invalid` (presented and rejected).

**An accepted credential establishes:**
- the request carried a credential that the app-supplied verifier accepted
  when `run` executed, and
- the verifier mapped that credential to this `actor` value.

**It does not establish:**
- that a particular human sent the request,
- that the actor still holds any role, membership or relationship (that is
  authorization, checked against current domain state at a defined point, Q5),
- anything about the request body or the rest of the request,
- freshness beyond the verifier's own checks (expiry, revocation list).

**Composition:**
- `a.orElse b` tries `b` only when `a` found *no* credential. A present but
  invalid credential is final. A bad bearer token is never downgraded to Basic
  or to anonymous.
- `requireAuth`: missing or invalid → 401 with the combined challenge.
- `optionalAuth`: missing → anonymous, invalid → 401.
- 403 is never produced by authentication. It is reserved for policy denial.
  Where existence must stay private, the app answers 404 instead (M5).

**Trust:** the verifier (token table, JWT verification, password check) is
app code or crypto-library code, and is assumed. The M6 evidence record names
it.
