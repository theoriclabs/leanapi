# Changelog

## 0.1.0 (2026-09-24): first release

LeanAPI is an API server for Lean 4, in the spirit of Express and FastAPI.

- **Routing:** path parameters, typed or not (`/items/{item_id}`, `{id:nat}`); route groups; `404` vs `405` with `Allow`; automatic `HEAD` and `OPTIONS`; conflicting routes rejected at compile time.
- **Requests:** handlers take their inputs as arguments: `Path`, `QueryParam "name"` (new), `QueryParams` (a record), `Header "name"`, cookies, `Body` (JSON or form), multipart. Invalid input is a `422` naming the field.
- **Responses:** JSON, text, `Created` (201 with `Location`), `NoContent`, ETags and conditional requests, cookies. Errors are RFC 9457 `application/problem+json`.
- **Middleware:** `cors`, `accessLog`, `requestId`, `recover`, `timeout`, `rateLimit`, `securityHeaders`, `health`, `trustedProxy`.
- **Auth:** bearer tokens, Basic, session cookies, HS256 JWT, scrypt password hashes.
- **Serving:** `app.listen 3000`, or `app.listenWith state 3000` for in-memory state (new), with graceful shutdown on Ctrl-C and SIGTERM.
- **Examples:** Hello World; path, query and body; middleware, headers and auth, in `examples/starter`. CI checks that each compiles, matches the README, and answers as the README shows.
