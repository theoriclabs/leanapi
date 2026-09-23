# Typed endpoints: design principles

Status: design, 2026-09-23. Implemented in `LeanApi/Http/Endpoint.lean`; the Notes example is written in it.

**The goal:** read an endpoint's type signature and know what the request does. That means knowing:
- what it takes, and from where;
- whether it can change state;
- what it answers on success;
- every way it can fail.

The body is then plain domain logic. It has no `Req`, no `Res`, no locks, and no status codes.

```lean
/-- Edit one of my notes, if it hasn't changed since `rev`. -/
def editNote (me : Auth User) (id : Path NoteId) (rev : IfMatch Rev) (edit : Body NoteEdit) :
    Writes State (Except EditError (Versioned NoteView))
```

## Principles

**1. The signature is the specification.**
- Every input is a parameter, and its *type* names where it comes from: `Auth`, `Path`, `Query`, `Body`, `Header`, `IfMatch`, `Fresh…`.
- The return type names three things:
  - the effect on state: `Reads` or `Writes`, or pure;
  - the success shape: `Created`, `Versioned`, `Paged`, `NoContent`, or a JSON value;
  - the failure set: `Except ε`, where `ε` is an ordinary inductive type listing every failure.
- Nothing about the request is hidden in the body.

**2. The whole request is a pure function.**
- `Reads σ α := σ → α` and `Writes σ α := σ → σ × α`.
- Every typed endpoint means `Env → Req → σ → Res × σ`, including authentication and decoding.
- Randomness and time arrive in `Env` (`FreshToken`, `Now`), not as ambient effects, so the same inputs give the same answer.
- The runtime draws a fresh `Env` and runs the whole request atomically against a state backend. Authentication and the write therefore see one snapshot.
- Code that needs arbitrary `IO` is written as a plain `Route` (principle 5), where it is visibly outside the typed, provable surface.

**3. Types carry the invariants the framework relies on.**
- **Statuses are typed.**
  - A success status is `{n // 200 ≤ n ∧ n < 300}`.
  - An error status is `{n // 400 ≤ n ∧ n < 600}`.
  - A failure cannot be answered with a 2xx, and a success cannot carry a 4xx.
- **Effects are an index.**
  - Each handler type has an `Effect` (`pure`, `reads`, `writes`), computed from its signature by instance resolution.
  - A `GET` or `HEAD` endpoint carries a proof that its effect is safe, discharged by `decide` when the endpoint is built.
  - A `GET` that writes is a compile error, not a code-review comment.
- **Path arity is checked.** Each `Path` parameter fills the next `{…}` of the template, in order. `api!` checks at compile time that the counts agree, and rejects conflicting routes as `routes!` does.
- **Values are validated at the boundary.** Inputs decode through the domain's smart constructors (`FromParam`, `FromBody`, `SmartCtor`). A handler only ever receives valid values. Invalid input becomes a 422 that lists every bad field.

**4. Nothing is hardcoded; everything is an instance.**
- **Inputs** are an open class, `FromRequest σ α`. `Auth`, `Path` and the others are library instances, and an app can add its own.
- **Outputs** are open classes: `ToResponse α` for success shapes, `ToProblem ε` for failures.
- **State** goes through a `Store σ` interface (`read`, `modify`). The in-memory backend (`Store.ofMutex`) is one implementation; a LeanDB-backed store is another.
- **Authentication** is `Authenticates σ α`: a pure check of the request against the state and the environment. The helpers `sessions`, `passwords` and `jwt` (verified at `Env.now`) cover the common schemes. Different actor types (`User`, `ByPassword`) name different schemes in the signature.

**5. The low level stays available.**
- `Endpoint` compiles to an ordinary `Route`, so typed endpoints and hand-written `Route.get … fun req => …` handlers share one router, middleware stack and test client.
- Typed endpoints are the default, not a cage.

**6. The typed surface is introspectable.**
- `Api.describe` prints every endpoint with its full signature, as elaborated.
- Each endpoint records its effect, path arity and input kinds. Documentation (OpenAPI) and proofs start from the same data instead of re-deriving it.

**7. The API is the model.**
- `Api.toSys` makes every typed API a `Props.Sys`, so the property library applies to the API itself, not to a separate model.
- `Handler` carries its laws as proofs, computed by instance resolution:
  - a safe handler never changes the state;
  - `Preserved I h` states what preserving `I` requires of `h`: nothing for `Reads`, "the state function preserves `I`" for `Writes`.
  - `Isolated R h` states what isolation requires: every input extracted alike in related states (automatic for inputs that don't read the state), `Auth` narrowing the relation to the actor's view (`ViewOf σ α`), and `Reads`/`Writes` answering alike.
- Three theorems hold for every typed API:
  - `Api.step_safe`: GET and HEAD never change the state.
  - `Api.inductive_of`: an invariant holds in every reachable state once each endpoint's `Preserved` obligation is discharged.
  - `Api.noninterference`: for a request authenticated as `p`, the whole response depends only on `p`'s view, once each endpoint's `Isolated` obligation is discharged.
- private-games is written this way (`PrivateGames/Api.lean`). On the typed API itself:
  - validity and unique ids (`ApiProofs.lean`) rest on the domain's `preserves` theorems;
  - isolation and existence privacy (`ApiIsolation.lean`) come from `Api.noninterference`, with about a hundred lines of per-endpoint obligations.
- Today the typed API runs over an in-memory state, and the LeanDB service is a separate implementation checked against it. The vision (DESIGN §7.4) is one definition over LeanDB query *values*: read-only by construction, with a pure meaning (`selectSpec`) for the proofs and SQL for production.

## Error semantics

Parameters are extracted left to right.

| Situation | Answer |
|---|---|
| Authentication fails | 401, with the challenge |
| Wrong `Content-Type` | 415 |
| Body is not parseable (JSON or form) | 400 |
| Any field fails to decode | 422, listing every invalid field across all remaining parameters, not just the first |
| Handler returns `Except.error e` | `ToProblem.status e` (4xx or 5xx, by type) with an RFC 9457 body |
| Handler returns a success value | `ToResponse`: 200 by default; `Created` gives 201 (with `Location`); `NoContent` gives 204; `Versioned` adds an `ETag` |
