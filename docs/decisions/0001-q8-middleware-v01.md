# 0001. Middleware is trusted adapter code (Q8, v0.1 form)

Status: accepted, M1, 2026-09-22. Revisit in M7 (typed middleware stages).

## Context

DESIGN.md §5 and Q8: middleware can short-circuit requests, retry downstream
execution, rewrite responses, log data and run effects. A handler proof does
not cover any of that. `intent.md` allows v0.1 to copy the middleware model
from other ecosystems.

## Decision

- `Middleware := App → App` where `App := Req → IO Res`. Composition is
  ordinary function composition. `Stack.of [a, b, c]` runs `a` outermost.
- Middleware is **trusted**. No theorem LeanAPI states about a route covers
  the middleware around it. Any claim about exported routes lists the stack
  as an assumption, by name and in order (`Stack.describe`).
- Built-ins are kept narrow so the assumption is easy to review:
  `recover`, `requestId`, `accessLog` (logs target and metadata only, never
  bodies, headers or cookies), `cors`, `trustedProxy`, `timeout`, `health`,
  `headers` / `securityHeaders`.
- `timeout` answers 504 but cannot undo a commit that already happened. The
  handler keeps running until it checks for cancellation. Clients treat a
  504 as an unknown outcome and retry with an idempotency key (Q6).

## Consequences

- Plain handlers and middleware are as easy to write as in Express.
- The M6 evidence record lists "middleware stack X is trusted" as an
  assumption. M7 replaces this with typed stages that declare what they
  establish and what they may observe.
