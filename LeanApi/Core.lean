import LeanContract
import LeanContract.Envelope
import LeanContract.Http
import LeanApi.Publication
import LeanApi.Core.Flow
import LeanApi.Core.Op
import LeanApi.Core.Auth
import LeanApi.Core.Publish
import LeanApi.Core.Api
import LeanApi.Core.Memory

/-! # LeanApi.Core: operations and endpoints, portable

`import LeanDb.Model` and `import LeanApi.Core`, then `open LeanDb.Model LeanApi.Core`. No
sockets, SQLite or native code: the import closure is this library, `LeanContract`,
`LeanDb.Model`, `LeanOntology` and Lean, so it compiles with LeanJS too.

```
structure SignedIn where
  private mk ::
  id : Ref Member
  deriving Principal

def borrow (me : SignedIn) (book : Ref Book) : Op BorrowError (Ref Loan) := do
  let some b ← Book.find book | throw .notFound
  let now ← Clock.now
  let ⟨onShelf⟩ ← require (MayBorrow now b) .unavailable
  …

def api : Api := [
  post "/books/:book/loans" borrow,
  get  "/books/:book"       getBook
]
```

* `LeanApi.Core.Flow` — the operation IR: `RequestF` embeds LeanDB's `StorageRequest`s and adds
  the clock and authentication; `Flow`, `Flow.run`, `Algebra`; `Resources` (LeanDB's
  `StorageResources` plus `auth`), `portableResources`; `Operation`, `FlowMetadata`, `KdfStep`,
  `CredentialLink`, `RouteInput`.
* `LeanApi.Core.Op` — `Op`, `ReadOp`, `require`, `Clock.now`, `Now`, `Principal`, the lifts of
  `DB`/`Query`, `Op.mapError`, the `Empty` codecs.
* `LeanApi.Core.Auth` — `Password.hash`, `Auth.startSession`, `credential C.profile C.hash`
  (`C.verify`), `deriving Principal`.
* `LeanApi.Core.Publish` — `derive_operation f`: `f.Input`, `f.Requirements`,
  `f.bodyWithResources`, `f.operation`.
* `LeanApi.Core.Api` — `def api : Api := [post "/x" f, get "/y/:id" g]`, `Endpoint`, typed
  `api.f`.
* `LeanApi.Core.Memory` — `LeanApi.Memory`: operations in memory.
* `LeanContract` (operation contracts, codecs, the HTTP envelope, client generation) and
  `LeanApi.Publication` (the application assembly operations publish into) are imported too.

The native server is `LeanApi.Native` (`app% Name where api := api`). -/
