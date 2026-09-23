/-
  Second app for the reusable isolation theorem (M7): notes with sharing.
  A different policy from private-games: a note is visible to its owner and
  to everyone it is shared with. Only the owner may share or edit.

  The app proves the three `ScopedApp.Obligations` and gets response
  noninterference from `LeanApi.Proofs.ScopedApp.step_noninterference`
  without re-proving anything about routing, authentication order or decode.
-/
import LeanApi

namespace Notes.Shared

open LeanApi LeanApi.Proofs Lean

abbrev User := Nat

structure Note where
  id : Nat
  owner : User
  sharedWith : List User
  text : String
  deriving DecidableEq, Repr

def canSee (u : User) (n : Note) : Bool := n.owner == u || n.sharedWith.contains u

/-- Notes keyed by id. (A list-ordered world does not work once sharing
    changes visibility: two worlds with the same view for a user can order
    that user's newly visible note differently. Keying by id removes order
    from the observation. private-games avoids the issue only because no
    write changes participants.) -/
structure World where
  notes : Nat → Option Note
  sessions : List (String × User)
  nextId : Nat

/-- What `u` sees at id `i`. -/
def seen (u : User) (w : World) (i : Nat) : Option Note := (w.notes i).filter (canSee u)

structure SameView (u : User) (w₁ w₂ : World) : Prop where
  sessions : w₁.sessions = w₂.sessions
  notes : ∀ i, seen u w₁ i = seen u w₂ i
  nextId : w₁.nextId = w₂.nextId

inductive Op where
  | create | read | share | edit
  deriving DecidableEq, Repr

def entries : List (Op × Method × List Seg) :=
  [(.create, .post, [.lit "notes"]), (.read, .get, [.lit "notes", .param "id" .nat]),
   (.share, .post, [.lit "notes", .param "id" .nat, .lit "shares"]),
   (.edit, .put, [.lit "notes", .param "id" .nat])]

inductive Input where
  | create (text : String)
  | read (id : Nat)
  | share (id : Nat) (with_ : User)
  | edit (id : Nat) (text : String)

def decode : Op → Req → Except Res Input
  | .create, r => match r.bodyText? with
    | some t => .ok (.create t)
    | none => .error (Problem.badRequest "body").toRes
  | .read, r => match (r.param? "id").bind String.toNat? with
    | some i => .ok (.read i)
    | none => .error Problem.notFound.toRes
  | .share, r => match (r.param? "id").bind String.toNat?, (r.query? "user").bind String.toNat? with
    | some i, some u => .ok (.share i u)
    | _, _ => .error (Problem.badRequest "user").toRes
  | .edit, r => match (r.param? "id").bind String.toNat?, r.bodyText? with
    | some i, some t => .ok (.edit i t)
    | _, _ => .error (Problem.badRequest "body").toRes

def Input.need : Input → Option Nat
  | .create _ => none
  | .read i | .share i _ | .edit i _ => some i

/-- The scoped load: only what the actor sees. -/
def load (u : User) (w : World) (n : Option Nat) : Option Note × Nat :=
  (n.bind (seen u w), w.nextId)

inductive Plan where
  | respond (r : Res)
  | insert (n : Note)
  | replace (old new : Note)

def noteRes (n : Note) (status : Nat := 200) : Res :=
  Res.json (Json.mkObj [("id", Json.num n.id), ("text", .str n.text)]) status

def core (u : User) : Input → Option Note × Nat → Plan
  | .create t, (_, next) => .insert { id := next, owner := u, sharedWith := [], text := t }
  | .read _, (some n, _) => .respond (noteRes n)
  | .share _ v, (some n, _) =>
      if n.owner == u then .replace n { n with sharedWith := v :: n.sharedWith }
      else .respond Problem.forbidden.toRes
  | .edit _ t, (some n, _) =>
      if n.owner == u then .replace n { n with text := t } else .respond Problem.forbidden.toRes
  | _, (none, _) => .respond Problem.notFound.toRes

def put (w : World) (i : Nat) (n : Note) : World :=
  { w with notes := fun j => if j = i then some n else w.notes j }

/-- The guard on a replace: the stored note is still `old`, the actor sees
    it, and the write keeps the id. Sharing may change who sees `new`. -/
def replaceOk (u : User) (old new : Note) (w : World) : Bool :=
  seen u w old.id == some old && new.id == old.id

def run (u : User) : Plan → World → Res × World
  | .respond r, w => (r, w)
  | .insert n, w => (noteRes n 201, { put w w.nextId n with nextId := w.nextId + 1 })
  | .replace old new, w =>
    if replaceOk u old new w then (noteRes new, put w old.id new) else (Problem.notFound.toRes, w)

def authenticate (r : Req) (w : World) : Except Res User :=
  match bearerToken? r with
  | some t => match w.sessions.lookup t with
    | some u => .ok u
    | none => .error (unauthorized "Bearer")
  | none => .error (unauthorized "Bearer")

def app : ScopedApp where
  World := World
  Actor := User
  Op := Op
  Input := Input
  Need := Option Nat
  Slice := Option Note × Nat
  Plan := Plan
  SameView := SameView
  entries := entries
  authenticate := authenticate
  decode := decode
  need := Input.need
  load := load
  core := core
  run := run

/-! ## The three obligations -/

theorem seen_put (v : User) (w : World) (i : Nat) (n : Note) (j : Nat) :
    seen v (put w i n) j = if j = i then (some n).filter (canSee v) else seen v w j := by
  simp only [seen, put]; split <;> rfl

theorem put_view {v : User} {w₁ w₂ : World} (h : SameView v w₁ w₂) (i : Nat) (n : Note) :
    ∀ j, seen v (put w₁ i n) j = seen v (put w₂ i n) j := by
  intro j; rw [seen_put, seen_put, h.notes j]

theorem replaceOk_view {u : User} {old new : Note} {w₁ w₂ : World} (h : SameView u w₁ w₂) :
    replaceOk u old new w₁ = replaceOk u old new w₂ := by
  simp only [replaceOk, h.notes old.id]

theorem obligations : app.Obligations where
  auth_view r w₁ w₂ h := by
    show authenticate r w₁ = authenticate r w₂
    have hs : w₁.sessions = w₂.sessions := (h (0 : User)).sessions
    simp only [authenticate, hs]
  load_view u w₁ w₂ n h := by
    show load u w₁ n = load u w₂ n
    simp only [load, h.nextId]
    congr 1
    cases n with
    | none => rfl
    | some i => exact h.notes i
  run_view u p w₁ w₂ h := by
    show (run u p w₁).1 = (run u p w₂).1 ∧ app.SameViews (run u p w₁).2 (run u p w₂).2
    cases p with
    | respond r => exact ⟨rfl, h⟩
    | insert n =>
      have hn := (h u).nextId
      refine ⟨rfl, fun v => ⟨(h v).sessions, ?_, by simp [run, hn]⟩⟩
      intro j
      show seen v (put w₁ w₁.nextId n) j = seen v (put w₂ w₂.nextId n) j
      rw [hn]; exact put_view (h v) _ n j
    | replace old new =>
      simp only [run, replaceOk_view (h u)]
      split
      · exact ⟨rfl, fun v => ⟨(h v).sessions, put_view (h v) old.id new, (h v).nextId⟩⟩
      · exact ⟨rfl, h⟩

/-- **Isolation for notes-with-sharing**, from the reusable theorem. What a
    user sees (including notes shared with them, and whether a note exists)
    does not depend on notes they cannot see. -/
theorem isolation (r : Req) {w₁ w₂ : World} (h : app.SameViews w₁ w₂) :
    (app.step r w₁).1 = (app.step r w₂).1 ∧ app.SameViews (app.step r w₁).2 (app.step r w₂).2 :=
  app.step_noninterference obligations r h

end Notes.Shared
