# LAPI-11: Endpoints over LeanDB read like the rest: one `api!`, no `fun _ =>`, no name clash

**Repo:** theoriclabs/leanapi · **Area:** `LeanApi/Http/DbEndpoint.lean`, `LeanApi/Http/DbProblem.lean`, `LeanApi/Http/Extract.lean`, `examples/private-games/PrivateGames/DbApi.lean` · **Priority:** P2 · **Size:** M
**Depends on:** LAPI-02 (done). **Enables:** LAPI-06 (`DbApi.step`), LAPI-09 (the blog shows `api!`).

## Problem

LAPI-02 made LeanDB programs endpoint results. Four things make the resulting code read worse than an in-memory endpoint:

1. **Every write endpoint starts with `fun _ =>`** (`DbApi.lean:82, 125, 137`). `Tx s ε ρ := (σ : Type) → Txn σ s ε ρ` (`DbEndpoint.lean:191`) takes the transaction index explicitly, so each body must bind it. The signature says `Tx`, but the body shows how `Tx` is encoded.
2. **Two API types and two macros.** `DbApi`/`dbapi!` sit next to `Api`/`api!`, and `dbapi!` repeats `api!`'s checks (template syntax, path arity, route conflicts, recorded signature; `DbEndpoint.lean:558-605`). There is no `DbApi.step`, so a theorem about the games API has to say `gamesApi.toApi.step`, not `gamesApi.step` as the blog does.
3. **`LeanApi.Query` (the query-string input) clashes with `LeanDb.Query`**, so app code writes `LeanDb.Query Games [GameRow] …` and `LeanDb.Query.from` (`DbApi.lean:44-45`).
4. **`WithReferrers` renders `reprStr who` into JSON** (`DbProblem.lean:218`): the wire name of a referencing table is Lean's `Repr` output, and the instance needs a `Repr` of an `if`-defined type.

## Proposal

1. **Make the transaction index implicit:** `abbrev Tx (s ε ρ : Type) [IsSchema s] := {σ : Type} → Txn σ s ε ρ`. Lean introduces the implicit binder itself, so a body is just `do …`. Checked in a scratch file against LeanDB M14c:
   - the body needs no binder;
   - instance resolution goes through the arrows (`Nat → Tx …`);
   - `Txn.denote (h (σ := Unit))` runs it;
   - a `Current σ α` in the result is still rejected (the ST-style guarantee stays).

   `DbProg`'s write case and `Handler`/`DbHandler` for `Tx` change to match (`p Unit` becomes `p (σ := Unit)`). Helpers such as `keyed` and `writeStep` keep an ordinary `σ`.
2. **One macro.** `api!` elaborates a list of `DbEndpoint`s to `DbApi s` and a list of `Endpoint`s to `Api σ`, by the expected type. The checks move into one function used for both. `dbapi!` stays as a deprecated alias for one release. Add `DbApi.step := api.toApi.step` and `DbApi.runAll`, so `gamesApi.step env r s` type-checks (LAPI-06 adds `DbApi.served`).
3. **Rename LeanAPI's query-string input to `QueryParams α`**, with `@[deprecated] abbrev Query := QueryParams` for one release. The clash remains while the alias exists; apps that open both namespaces switch to `QueryParams` to lose it.
4. **`WithReferrers` names the referrer from the schema:**
   - the source table is `Entity.tableName (Source r)`, via `HasReferencedBy.sourceEntity`;
   - the column is `HasReferencedBy.columnName r`;
   - the extension is `{"referrers": {"table": …, "column": …, "rows": n}}`, and the instance drops its `Repr` requirement.

## Acceptance criteria

- `DbApi.lean`:
  - has no `fun _ =>`, and no `LeanDb.` qualification on `Query`;
  - `gamesApi : DbApi Games := api! [...]`.
- Existing `#guard_msgs` tests pass: a `GET` returning a `Tx` does not compile, and a path-arity mismatch is reported with the handler's signature. A new one: a `Tx` handler whose result mentions `Current σ α` does not compile.
- `describe` prints `Tx …`/`Read …` signatures as before.
- `WithReferrers`' 409 names the table and column (a test with a restrict key).
- The blog's `gamesApi` excerpt shows `api!`, and `check_blog.sh` passes the same blocks as before.
- CI passes (build, tests, axiom audit, README, evidence).

## Tests

- `tests/Tests/DbEndpoint.lean`: the endpoints rewritten without `fun _ =>`, plus the `Current` escape test.
- The `api!` tests in `tests/Tests/Endpoint.lean` run for both endpoint kinds.

## Compatibility

- **Source-compatible for one release:** `dbapi!` and `Query` remain, deprecated.
- **A breaking change for handlers that bind `σ` explicitly** (`fun σ => …`). They must drop the binder or write `fun {σ} => …`.
- **`WithReferrers`' JSON changes** (opt-in wrapper; no example uses it).
