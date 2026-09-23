/-
  Spike candidate (a): a pure `decide` inside an effectful shell.

  The shell is ordinary code: load the game through the scoped
  repository, call the pure decision, commit against the revision.
  "All code paths" for a proof means: the decision function (proved in
  Domain.Proofs) plus the shell, which is small and reviewed, and whose
  model (`shellModel`) is the thing M6 proves things about.

  Tried here: PlayMove (custom theorem), ListMyGames with pagination, and
  an external-effect intent (a notification on game end).
-/
import PrivateGames.Domain.Proofs

namespace PrivateGames.Spike.Shell

/-- The store interface the shell sees. Every read takes the actor. -/
structure Repo (m : Type → Type) where
  loadVisible : PlayerId → GameId → m (Option Game)
  listVisible : PlayerId → (offset limit : Nat) → m (List Game)
  commit : (old new : Game) → m Bool
  enqueue : String → m Unit

/-- An intent to notify, decided in pure code, delivered by a worker. -/
def endIntent (before after : Game) : List String :=
  if before.outcome = .ongoing ∧ after.outcome ≠ .ongoing then [s!"game {after.id} ended"] else []

inductive ShellError where
  | notFound
  | domain (e : DomainError)
  | conflict
  deriving Repr, DecidableEq

/-- The pure core: everything between load and commit. -/
def playMoveCore (p : PlayerId) (loaded : Option Game) (e : Revision) (c : Cell) :
    Except ShellError (Game × Game) :=
  match loaded with
  | none => .error .notFound
  | some g =>
    match PrivateGames.playMove p e c g with
    | .error err => .error (.domain err)
    | .ok g' => .ok (g, g')

/-- The shell: load, core, commit, enqueue. -/
def playMove [Monad m] (repo : Repo m) (p : PlayerId) (gid : GameId) (e : Revision) (c : Cell) :
    m (Except ShellError Game) := do
  match playMoveCore p (← repo.loadVisible p gid) e c with
  | .error err => return .error err
  | .ok (g, g') =>
    if ← repo.commit g g' then
      for n in endIntent g g' do repo.enqueue n
      return .ok g'
    else return .error .conflict

def listMine [Monad m] (repo : Repo m) (p : PlayerId) (page per : Nat) : m (List Game) :=
  repo.listVisible p ((page - 1) * per) per

/-- Custom theorem, candidate (a): a successful core returns a game the
    caller participates in, whatever was loaded. It holds even if the
    repository broke its scoping contract, because `playMove` itself
    refuses non-participants. -/
theorem playMoveCore_participant {p : PlayerId} {l : Option Game} {e : Revision} {c : Cell} {g g' : Game}
    (h : playMoveCore p l e c = .ok (g, g')) : visible p g' = true := by
  unfold playMoveCore at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i g1 hdec
      cases h
      have hp := (PrivateGames.playMove_ok hdec).1
      have heq := (PrivateGames.playMove_ok hdec).2.2.2.2.2
      subst heq
      simpa [visible, Game.isParticipant] using hp

/-! The same shell over a pure in-memory store, for tests and the model. -/

structure Mem where
  games : List Game
  outbox : List String := []

abbrev MemM := StateM Mem

def memRepo : Repo MemM where
  loadVisible p gid := do return (← get).games.find? fun g => g.id = gid ∧ visible p g
  listVisible p off lim := do return (((← get).games.filter (visible p)).drop off).take lim
  commit old new := do
    let s ← get
    if s.games.contains old then
      set { s with games := s.games.map fun g => if g = old then new else g }
      return true
    else return false
  enqueue n := modify fun s => { s with outbox := s.outbox ++ [n] }

/-- Pagination is over the scoped list, so every page is visible rows only. -/
theorem listMine_visible (p : PlayerId) (page per : Nat) (s : Mem) :
    ∀ g ∈ ((listMine memRepo p page per).run s).1, visible p g = true := by
  intro g hg
  simp only [listMine, memRepo, StateT.run, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure] at hg
  have := List.mem_of_mem_take hg
  have := List.mem_of_mem_drop this
  exact (List.mem_filter.mp this).2

end PrivateGames.Spike.Shell
