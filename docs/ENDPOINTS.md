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

**2. The handler is a pure function.**
- `Reads σ α := σ → α` and `Writes σ α := σ → σ × α`.
- The framework runs them atomically against a state backend.
- Randomness and time are inputs (`FreshToken`), not ambient effects, so the same inputs give the same answer.
- `IO` is allowed as an explicit escape hatch, and it shows in the signature.

**3. Types carry the invariants the framework relies on.**
- **Statuses are typed.**
  - A success status is `{n // 200 ≤ n ∧ n < 300}`.
  - An error status is `{n // 400 ≤ n ∧ n < 600}`.
  - A failure cannot be answered with a 2xx, and a success cannot carry a 4xx.
- **Effects are an index.**
  - Each handler type has an `Effect` (`pure`, `reads`, `writes`, `io`), computed from its signature by instance resolution.
  - A `GET` or `HEAD` endpoint carries a proof that its effect is safe, discharged by `decide` when the endpoint is built.
  - A `GET` that writes is a compile error, not a code-review comment.
- **Path arity is checked.** Each `Path` parameter fills the next `{…}` of the template, in order. `api!` checks at compile time that the counts agree, and rejects conflicting routes as `routes!` does.
- **Values are validated at the boundary.** Inputs decode through the domain's smart constructors (`FromParam`, `FromBody`, `SmartCtor`). A handler only ever receives valid values. Invalid input becomes a 422 that lists every bad field.

**4. Nothing is hardcoded; everything is an instance.**
- **Inputs** are an open class, `FromRequest σ α`. `Auth`, `Path` and the others are library instances, and an app can add its own.
- **Outputs** are open classes: `ToResponse α` for success shapes, `ToProblem ε` for failures.
- **State** goes through a `Store σ` interface (`read`, `modify`). The in-memory backend (`Store.ofMutex`) is one implementation; a LeanDB-backed store is another.
- **Authentication** is `Authenticates σ α`: how to obtain an actor of type `α`. Helpers build it from pure lookups over the state (`sessions`, `passwords`), and any `Authenticator` (JWT, …) plugs in. Different actor types (`User`, `ByPassword`) name different schemes in the signature.

**5. The low level stays available.**
- `Endpoint` compiles to an ordinary `Route`, so typed endpoints and hand-written `Route.get … fun req => …` handlers share one router, middleware stack and test client.
- Typed endpoints are the default, not a cage.

**6. The typed surface is introspectable.**
- `Api.describe` prints every endpoint with its full signature, as elaborated.
- Each endpoint records its effect, path arity and input kinds. Documentation (OpenAPI) and proofs start from the same data instead of re-deriving it.

**7. It lines up with the proofs.**
- A `Reads` endpoint cannot change state by its type, so "safe reads" needs no hand proof.
- A `Writes` handler is exactly the `σ → σ × α` shape that `invariant` and `preserves` reason about.
- The API a user writes and the model the proofs are about become the same functions.

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
