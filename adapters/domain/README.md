# Optional native domain adapter

`LeanApiDomain` serves portable domain code (LeanReact's `LeanApp.Domain`: plain operations
returning `Op`/`ReadOp`, `deriving Entity`, constraints, `def api : Api := […]`) natively over
SQLite (LeanDB's storage hooks), and keeps the milestone 1 `command%`/`query%`/`auth%` surface.

A LeanReact `App` (`def app : App where api := api; pages := ["/orders/:order" ==> orderPage, …]`)
is served as it is:

```lean
app% server where
  app := Shop.app                                      -- its `api` and its `pages`
  migrations := [addNote := Shop.Order.addField note (fill := "")]

def main (args : List String) : IO UInt32 := server.main args
```

- The `api` gives the HTTP routes; the `pages` are served as HTML (a navigation, `Accept:
  text/html`, gets the page where a GET endpoint shares the path) and routed in the browser by
  the compiled `App.component`.
- Authentication is read from the domain: the one entity declared with
  `credential C.profile C.hash` next to the `api`, whose profile is the signed-in principal;
  the operations whose flow starts a session (`Auth.startSession`) sign the browser in.

An API with no accounts (no credential, no sessions, no pages):

```lean
app% Name where
  api := api                                           -- post "/games" …, get "/games/:game" …
  migrations := [addNote := Shop.Order.addField note (fill := "")]   -- optional
```

- The schema is the domain entities of the api's namespace (the root namespace for a root
  `api`). `PublicApp s` has no profile type and no auth storage, so no account table exists.
- Every operation takes no actor. One that needs a signed-in user (`SignedIn`,
  `Option SignedIn`) is an elaboration error naming it; one that hashes a password or starts
  a session is refused when the app is assembled (`app.accounts_required`).
- Presented credentials (cookies, `Authorization`) are ignored, and commands need no Origin or
  CSRF check: there is no ambient credential to protect (see decision 9 in the handoff).

Without pages, or with explicit routes:

```lean
app% Shop where
  authentication := Shop.Customer with Shop.CustomerCredential   -- an authored credential entity
  routes := [get "/orders/:order/receipt" Shop.receipt.operation]
  pages := []
  api := Shop.api                                                 -- post "/orders" …, get "/orders/:order" …
  migrations := [addNote := Shop.Order.addField note (fill := "")]

def main (args : List String) : IO UInt32 := Shop.main args { database := "shop.db" }
```

- Routes: explicit `(method, template, operation)` entries; `:name` binds the input field
  `name` (checked at elaboration); `get` only for read-only operations; only listed routes are
  served, in `/api/manifest` and in the generated client.
- Replies: `{"ok": v}`, `{"error": "ctor"}`, `{"error": "unauthorized"}` (framework failures
  carry their precise code in `x-leanapp-error`). Milestone 1 `operations := […]` apps keep
  their Contract envelope. A stored row or value that does not decode or fails its check
  (a raw-SQL edit; a `represent`ed value its checker rejects) is a 500 with code
  `storage.corrupt`; the table, column and reason stay in the server.
- Sessions: browsers get an HttpOnly cookie plus CSRF; other clients send
  `Authorization: Bearer <token>`, obtained with `Accept: application/vnd.leanapp.token`.
- Authored sign-up/sign-in: `Password.hash`, `Credential.verify` and `Auth.startSession` run
  natively; the KDF work an operation declares (`FlowMetadata.kdf`) is prepared before writer
  admission under `KDFGate`, with equal dummy work for a missing profile.
- `main args` runs LeanDB's migration gate (`migrate --check`, `migrate`, or apply at startup);
  `AppConfig.port` defaults to 8080, overridable with `LEANAPP_PORT` and the other
  `LEANAPP_*` variables. The executable finds its browser bundle from its build tree.

Fixtures: `tests/LibraryApp.lean` (a library-loans app with a LeanReact `App`, the generality
fixture), `tests/CounterApp.lean` (public counters, no accounts), `tests/PostApp.lean`,
`tests/PartifulBefore.lean` and `tests/RouteChecks.lean`; the acceptance scripts under `scripts/`.
See [the milestone 2 handoff](../../docs/ddd-m2-handoff.md).
