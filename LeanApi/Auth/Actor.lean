/-
  The authenticated actor. Authentication makes one (`LeanApi/Http/Endpoint.lean`);
  handlers, database programs and row policies take one. This module
  imports nothing, so business rules can name the actor without depending
  on HTTP (`architecture/Architecture/Apps.lean`).
-/
namespace LeanApi

/-- The authenticated actor, of the type the scheme produces.

    The constructor is private: an `Auth α` is made only by authentication
    (the `FromRequest` and `Handler` instances in
    `LeanApi/Http/Endpoint.lean`, and `DbEndpoint`'s), through
    `Internal.authOf`. Application code cannot write
    `⟨otherUser⟩ : Auth UserId`, so a handler, or a row-policy view built
    from `me`, acts for the caller the request authenticated and no one else.
    `scripts/check_private_escapes.sh` (CI) refuses any use of
    `LeanApi.Internal` outside `LeanApi/` and `tests/`. -/
structure Auth (α : Type) where
  private mk ::
  val : α

/-! Framework internals. Lean 4 has no friend modules, so the framework's
    other files reach private constructors through this namespace, and CI
    (`scripts/check_private_escapes.sh`) refuses its use anywhere else. -/
namespace Internal

/-- An `Auth` for an actor that authentication has produced. For the
    framework's authentication paths only. -/
def authOf (who : α) : Auth α := ⟨who⟩

end Internal

end LeanApi
