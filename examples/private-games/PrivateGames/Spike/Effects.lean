/-
  Spike candidate (b): handlers written in a small effect language.

  `Prog` is a free monad over operations the framework controls:
  scoped reads, revision commits and effect intents. It has no ambient IO.
  The only way a handler can observe a game is `readVisible`, which is
  scoped by the actor the interpreter was given, not by anything the
  handler supplies. So "all code paths" is literal: every program, not
  just the ones written so far, goes through these constructors.

  Tried: PlayMove, ListMyGames with pagination, an effect intent, and a
  custom theorem quantified over ALL programs.
-/
import PrivateGames.Domain.Proofs

namespace PrivateGames.Spike.Effects

inductive Prog (α : Type) where
  | pure (a : α)
  | readVisible (gid : GameId) (k : Option Game → Prog α)
  | listVisible (offset limit : Nat) (k : List Game → Prog α)
  | commit (old new : Game) (k : Bool → Prog α)
  | intent (msg : String) (k : Prog α)

/-- The visibility-scoped lookup the interpreter performs. -/
def findVisible (p : PlayerId) (gid : GameId) (gs : List Game) : Option Game :=
  gs.find? fun g => g.id == gid && visible p g

namespace Prog

def bind : Prog α → (α → Prog β) → Prog β
  | .pure a, f => f a
  | .readVisible g k, f => .readVisible g fun x => bind (k x) f
  | .listVisible o l k, f => .listVisible o l fun x => bind (k x) f
  | .commit a b k, f => .commit a b fun x => bind (k x) f
  | .intent m k, f => .intent m (bind k f)

instance : Monad Prog where
  pure := .pure
  bind := bind

def read (g : GameId) : Prog (Option Game) := .readVisible g .pure
def list (o l : Nat) : Prog (List Game) := .listVisible o l .pure
def commitRev (a b : Game) : Prog Bool := .commit a b .pure
def emit (m : String) : Prog Unit := .intent m (.pure ())

end Prog

structure Mem where
  games : List Game
  outbox : List String := []

/-- The interpreter: the actor is fixed here, outside the program. Commits
    are accepted only for a game the actor can see. -/
def run (p : PlayerId) : Prog α → Mem → α × Mem
  | .pure a, s => (a, s)
  | .readVisible gid k, s => run p (k (findVisible p gid s.games)) s
  | .listVisible o l k, s => run p (k (((s.games.filter (visible p)).drop o).take l)) s
  | .commit old new k, s =>
      if s.games.contains old ∧ visible p old then
        run p (k true) { s with games := s.games.map fun g => if g = old then new else g }
      else run p (k false) s
  | .intent m k, s => run p k { s with outbox := s.outbox ++ [m] }

/-- What a program read: every game handed to a continuation. -/
def reads (p : PlayerId) : Prog α → Mem → List Game
  | .pure _, _ => []
  | .readVisible gid k, s =>
      let r := findVisible p gid s.games
      r.toList ++ reads p (k r) s
  | .listVisible o l k, s =>
      let r := ((s.games.filter (visible p)).drop o).take l
      r ++ reads p (k r) s
  | .commit old new k, s =>
      if s.games.contains old ∧ visible p old then
        reads p (k true) { s with games := s.games.map fun g => if g = old then new else g }
      else reads p (k false) s
  | .intent m k, s => reads p k { s with outbox := s.outbox ++ [m] }

inductive Err where
  | notFound
  | domain (e : DomainError)
  | conflict
  deriving Repr

def playMove (p : PlayerId) (gid : GameId) (e : Revision) (c : Cell) : Prog (Except Err Game) := do
  match ← Prog.read gid with
  | none => return .error .notFound
  | some g =>
    match PrivateGames.playMove p e c g with
    | .error err => return .error (.domain err)
    | .ok g' =>
      if ← Prog.commitRev g g' then
        if g'.outcome ≠ Outcome.ongoing then Prog.emit s!"game {gid} ended"
        return .ok g'
      else return .error .conflict

def listMine (page per : Nat) : Prog (List Game) := Prog.list ((page - 1) * per) per

/-- Custom theorem, candidate (b), over EVERY program: whatever a handler
    does, every game it reads is visible to the actor. Restricted logical
    reads hold by construction of the interpreter. -/
theorem reads_visible (p : PlayerId) : ∀ (prog : Prog α) (s : Mem), ∀ g ∈ reads p prog s, visible p g = true := by
  intro prog
  induction prog with
  | pure a => intro s g h; simp [reads] at h
  | readVisible gid k ih =>
    intro s g h
    simp only [reads, List.mem_append] at h
    rcases h with h | h
    · cases hf : findVisible p gid s.games with
      | none => simp [hf] at h
      | some g0 =>
        simp [hf] at h; subst h
        have := List.find?_some hf
        simp at this; exact this.2
    · exact ih _ s g h
  | listVisible o l k ih =>
    intro s g h
    simp only [reads, List.mem_append] at h
    rcases h with h | h
    · exact (List.mem_filter.mp (List.mem_of_mem_drop (List.mem_of_mem_take h))).2
    · exact ih _ s g h
  | commit old new k ih =>
    intro s g h
    simp only [reads] at h
    split at h
    · exact ih _ _ g h
    · exact ih _ _ g h
  | intent m k ih =>
    intro s g h
    exact ih _ g h

/-- And writes: a commit only ever changes a game the actor can see. -/
theorem commit_scoped (p : PlayerId) (old new : Game) (k : Bool → Prog α) (s : Mem)
    (h : visible p old = false) : run p (.commit old new k) s = run p (k false) s := by
  simp [run, h]

end PrivateGames.Spike.Effects
