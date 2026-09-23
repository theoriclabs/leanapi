/-
  Typed middleware stages (Q8, second form; decision 0013).

  A `Stage` declares what it may observe and what it may do, as data:
  * `observes`: request parts it reads (`method`, `path`, `headers [..]`,
    `body`, ...)
  * `effects`: whether it may short-circuit, rewrite the response, rewrite
    the request, or run IO beyond its declaration.
  and it is built from a restricted form, not an arbitrary `App → App`:
  * `Stage.guard`: may refuse with a response computed from the observed
    request parts only; otherwise passes the request through unchanged.
  * `Stage.decorate`: may add response headers computed from the observed
    request parts only; never changes status or body.

  For these forms the contract is a theorem, not an assumption:
  `guard_transparent` (when it passes, the inner app sees the exact
  request) and `decorate_preserves` (status and body are the inner app's).
  So a stack of typed stages can enter a theorem: the inner app's
  status/body claims survive `decorate`, and `guard` either answers with
  something independent of hidden data or is transparent.
-/
import LeanApi.Http.Middleware

namespace LeanApi

/-- Request parts a stage reads. -/
inductive Observes where
  | method | path | query | headers (names : List String) | body | remote
  deriving Repr, BEq

/-- Restrict a request to what a stage declared it observes. -/
def Req.restrict (r : Req) (os : List Observes) : Req :=
  { method := if os.contains .method then r.method else .get
    path := if os.contains .path then r.path else []
    query := if os.contains .query then r.query else []
    headers := r.headers.filter fun (k, _) => os.any fun
      | .headers ns => ns.contains k
      | _ => false
    body := if os.contains .body then r.body else .empty
    remoteAddr := if os.contains .remote then r.remoteAddr else none }

inductive Stage where
  /-- Refuse (with a response) or pass unchanged. The decision sees only the
      restricted request. -/
  | guard (name : String) (observes : List Observes) (decide : Req → Option Res)
  /-- Add headers computed from the restricted request. -/
  | decorate (name : String) (observes : List Observes) (headers : Req → List (String × String))

namespace Stage

def name : Stage → String
  | .guard n .. | .decorate n .. => n

def describe : Stage → String
  | .guard n os _ => s!"{n} [guard; observes {repr os}]"
  | .decorate n os _ => s!"{n} [decorate; observes {repr os}]"

/-- The pure semantics: an app transformer over a pure app. -/
def applyPure (s : Stage) (app : Req → Res) : Req → Res :=
  match s with
  | .guard _ os d => fun r => match d (r.restrict os) with
    | some res => res
    | none => app r
  | .decorate _ os hs => fun r => (hs (r.restrict os)).foldl (fun acc (k, v) => acc.setHeader k v) (app r)

/-- The runtime form. -/
def toMiddleware (s : Stage) : NamedMiddleware :=
  match s with
  | .guard n os d => ⟨n, fun h r => match d (r.restrict os) with
    | some res => pure res
    | none => h r⟩
  | .decorate n os hs => ⟨n, fun h r => do
    let res ← h r
    pure ((hs (r.restrict os)).foldl (fun acc (k, v) => acc.setHeader k v) res)⟩

theorem setHeader_status (r : Res) (k v : String) : (r.setHeader k v).status = r.status := rfl
theorem setHeader_body (r : Res) (k v : String) : (r.setHeader k v).body = r.body := rfl

theorem foldl_setHeader (hs : List (String × String)) (r : Res) :
    (hs.foldl (fun acc (k, v) => acc.setHeader k v) r).status = r.status ∧
    (hs.foldl (fun acc (k, v) => acc.setHeader k v) r).body = r.body := by
  induction hs generalizing r with
  | nil => exact ⟨rfl, rfl⟩
  | cons h t ih => exact ih _

/-- A decorate stage never changes status or body. -/
theorem decorate_preserves (n : String) (os : List Observes) (hs : Req → List (String × String))
    (app : Req → Res) (r : Req) :
    ((Stage.decorate n os hs).applyPure app r).status = (app r).status ∧
    ((Stage.decorate n os hs).applyPure app r).body = (app r).body :=
  foldl_setHeader _ _

/-- When a guard passes, the inner app runs on the unchanged request. -/
theorem guard_transparent (n : String) (os : List Observes) (d : Req → Option Res)
    (app : Req → Res) (r : Req) (h : d (r.restrict os) = none) :
    (Stage.guard n os d).applyPure app r = app r := by
  simp [applyPure, h]

/-- A guard's refusal depends only on the observed parts: two requests that
    agree on them are refused identically. -/
theorem guard_observes (n : String) (os : List Observes) (d : Req → Option Res)
    (app : Req → Res) (r₁ r₂ : Req) (h : r₁.restrict os = r₂.restrict os) (res : Res)
    (hr : d (r₁.restrict os) = some res) :
    (Stage.guard n os d).applyPure app r₁ = res ∧ (Stage.guard n os d).applyPure app r₂ = res := by
  simp [applyPure, hr, ← h]

end Stage

def Stack.ofStages (ss : List Stage) : Stack := Stack.of (ss.map Stage.toMiddleware)

def describeStages (ss : List Stage) : String := "\n".intercalate (ss.map Stage.describe)

/-! Typed versions of the stateless built-ins. -/

def Stage.securityHeaders : Stage :=
  .decorate "securityHeaders" [] fun _ =>
    [("x-content-type-options", "nosniff"), ("referrer-policy", "no-referrer"), ("x-frame-options", "DENY")]

/-- Refuse bodies with the wrong media type before routing. -/
def Stage.requireJsonBodies : Stage :=
  .guard "requireJsonBodies" [.method, .headers ["content-type", "content-length", "transfer-encoding"]] fun r =>
    let hasBody := (r.header? "content-length").any (· != "0") || (r.header? "transfer-encoding").isSome
    if (r.method == .post || r.method == .put || r.method == .patch) && hasBody && r.contentType? != some "application/json"
    then some (Problem.make 415 (some "expected application/json")).toRes else none

end LeanApi
