# Changelog

## 0.1.0 (M1): HTTP toolkit

- Routing: method + path templates (`{id}`, `{id:int}`, `{id:nat}`, `{*rest}`),
  groups and prefixes, precedence by segment kind, conflict detection at
  `Router.build` and at elaboration time (`routes!`). 404 vs 405 with `Allow`,
  automatic `HEAD` and `OPTIONS`, trailing-slash policy (redirect / strict /
  ignore), dot segments refused.
- Extraction: typed path, query, header, cookie, JSON and form extractors;
  `FromParam` / `FromBody` / `SmartCtor` so domain constructors validate at
  the boundary; errors with field locations (`body.title`, `query.page`),
  accumulated across fields; 415 and 406.
- Per-route body limits enforced while streaming (413).
- Responses: builders for text, JSON, bytes, redirects, `Set-Cookie`;
  RFC 9457 `application/problem+json` errors; exceptions become a 500
  without internal details, logged under the request id.
- Middleware: `App → App`, ordered named stacks with `Stack.describe`;
  built-ins `recover`, `requestId`, `accessLog`, `cors`, `trustedProxy`,
  `timeout`, `health`, `securityHeaders`.
- Authentication interface: `Authenticator`, bearer / Basic / session cookie
  over app-supplied verifiers, `orElse`, `requireAuth`, `optionalAuth`, 401
  with `WWW-Authenticate`.
- Runtime: `serve` with graceful shutdown on SIGTERM/SIGINT; handlers run on
  dedicated threads; `Worker`/`Pool` bounded queues for blocking work.
- In-process test transport over `Std.Http.Server.serveConnection`.
- `examples/notes`.
