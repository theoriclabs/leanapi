# architecture/

This directory holds the shape of this codebase and its goals, written in Lean. `lake build` checks them.

| File | What it says |
|---|---|
| [Graph.lean](Architecture/Graph.lean) | The machinery. Import graphs, and what it means to conform to a design. `imports%` reads the build's import graph, and the `conforms` tactic checks it. |
| [Framework.lean](Architecture/Framework.lean) | LeanAPI's parts, and which part may use which. Plus the rules that follow for every chain of imports. |
| [Apps.lean](Architecture/Apps.lean) | The layers of an application (domain, schema, policies, API), checked on helpdesk, billing and scheduling. |
| [Goals.lean](Architecture/Goals.lean) | The project's goals as Lean statements. Each one is proved, open (with the ticket that proves it), or not yet statable (with the ticket that brings the words). |

## How the check works

1. **`imports% LeanApi`** is the import graph Lean compiled. It has one edge per `import` in a module under `LeanApi`, read from the environment.
2. **Each module belongs to one part.** A rule list decides which. A module in no part fails the build.
3. **`design`** is a small graph over the parts. The theorem `conforms` says every import follows a path of it. The kernel checks this one import at a time (`decide`, with no native code).
4. **Rules hold for chains of imports.** `Graph.Conforms.reaches` lifts the per-import check to chains. So "the property library never reaches the server" follows from one fact about the small design graph.

When a check fails, the error names the imports that break the design:

```text
these imports do not follow the design:
  LeanApi.Http.Endpoint (endpoints) imports LeanApi.Runtime.Server (server)
```

**Trusted:** `imports%` itself, a 14-line elaborator. The theorems are about the graph it returns.

## The rules

| Theorem | Says |
|---|---|
| `Framework.props_never_reach_the_server` | The property library reaches none of the server, `Std.Http`, the worker threads or LeanDB. Its theorems are about plain functions. |
| `Framework.endpoints_never_reach_the_transport` | Typed endpoints never reach the server or `Std.Http`. They hold `Api.step_safe` and `Api.noninterference`, so those theorems are about code with no sockets in it. |
| `Framework.database_never_reaches_the_transport` | The same, for database endpoints. |
| `Framework.endpoints_never_reach_leandb` | LeanDB is optional for HTTP-only applications. |
| `Framework.only_the_server_imports_std_http` | `Std.Http` changes between toolchains stay in one file. |
| `Apps.domain_is_plain_lean` | An application's domain reaches neither HTTP nor LeanDB (DESIGN §3.2). |
| `Apps.rules_never_reach_http` | Schema and policies reach `Auth`, never the rest of LeanAPI. Who may see a row depends on who is asking, not on how they logged in. |
| `Apps.nothing_reaches_the_api` | The API is the outermost layer. |

## What the first run found (2026-09-25)

Checked against `main` at `0f9aa9f`, the design failed on six imports. One prose claim was also false: the server module's header said it was the only module that touches `Std.Http`.

| Import | Fix |
|---|---|
| `Http.Endpoint` → `Runtime.Server`, for `Service` only | `Service` moved to `Http/Service.lean` |
| `Http.Request` → `Std.Http`, `Http.Response` → `Std.Http` | The conversions (`Method.ofStd?`, `Res.toStd`) moved into `Runtime/Server.lean`. The header's claim is now a theorem. |
| `PolicyView.Policy` → `LeanApi`, for `Auth` only | `Auth` moved to `Auth/Actor.lean`, which imports nothing |
| `Helpdesk.Policies` → `Http.DbEndpoint` | The `Auth` → program bridge (`TxAs.forAuth`) moved to `Helpdesk/Api.lean`. The same for scheduling and billing (`WriteAs.toTx`). |
| `Billing.Api` → `Billing.Bypass` | Removed: the library builds `Bypass` anyway |

## Changing things

- **New module:** add it to `rules` in its file.
- **New dependency between parts:** add an edge to `design`. If a rule theorem then fails, the design change breaks that rule, and the error says so.
- **A goal is proved:** change `.unstated`/`.open` to `.proved`, and update the list that `#guard_msgs` checks at the end of `Goals.lean`.
