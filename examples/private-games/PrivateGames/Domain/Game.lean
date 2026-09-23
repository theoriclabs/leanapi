/-
  The private-games domain: state, legality, outcomes, policy, decisions.
  Pure Lean. No HTTP, no SQL.

  The game is tic-tac-toe on a 3×3 board: small enough that the proofs are
  about isolation, revisions and idempotence rather than chess rules.
  (PLAN.md M3.1 allows "simplified if not convenient"; leanchess's rules
  could replace `Rules` without changing the other layers.)

  Specifications (DESIGN §2.4) are stated as `Prop`s: `Valid`, `Allowed`,
  `Transition`. The decisions `playMove` and `resign` are proved to accept
  only allowed commands, to follow `Transition`, and to preserve `Valid`.
-/
import PrivateGames.Domain.Values

namespace PrivateGames

inductive Mark where
  | x | o
  deriving DecidableEq, Repr

/-! ## State -/

structure Game where
  id : GameId
  /-- Moves first. -/
  x : PlayerId
  o : PlayerId
  timeControl : TimeControl
  /-- Cells in the order they were played; `x` plays the even positions. -/
  moves : List Cell
  /-- Who resigned, if anyone. -/
  resigned : Option PlayerId := none
  /-- Bumped by every accepted transition. -/
  rev : Revision := 0
  deriving DecidableEq, Repr

namespace Rules

def lines : List (Nat × Nat × Nat) :=
  [(0,1,2), (3,4,5), (6,7,8), (0,3,6), (1,4,7), (2,5,8), (0,4,8), (2,4,6)]

/-- The mark on square `i` after `moves`. -/
def markAt (moves : List Cell) (i : Nat) : Option Mark :=
  match moves.findIdx? (·.i == i) with
  | some k => some (if k % 2 == 0 then .x else .o)
  | none => none

def winner? (moves : List Cell) : Option Mark :=
  lines.findSome? fun (a, b, c) =>
    match markAt moves a, markAt moves b, markAt moves c with
    | some m, some m', some m'' => if m = m' ∧ m' = m'' then some m else none
    | _, _, _ => none

/-- No move was played after the game had a winner. -/
def legalHistory (moves : List Cell) : Bool :=
  (List.range moves.length).all fun k => (winner? (moves.take k)).isNone

end Rules

inductive Outcome where
  | ongoing
  | won (winner : PlayerId)
  | drawn
  | resigned (loser winner : PlayerId)
  deriving DecidableEq, Repr

namespace Game

def playerOf (g : Game) : Mark → PlayerId
  | .x => g.x
  | .o => g.o

def outcome (g : Game) : Outcome :=
  match g.resigned with
  | some p => .resigned p (if p = g.x then g.o else g.x)
  | none =>
    match Rules.winner? g.moves with
    | some m => .won (g.playerOf m)
    | none => if g.moves.length < 9 then .ongoing else .drawn

def toMove (g : Game) : PlayerId := if g.moves.length % 2 = 0 then g.x else g.o

def isParticipant (g : Game) (p : PlayerId) : Bool := p == g.x || p == g.o

def isFree (g : Game) (c : Cell) : Bool := !(g.moves.any (·.i == c.i))

def opened (id : GameId) (x o : PlayerId) (tc : TimeControl) : Game :=
  { id, x, o, timeControl := tc, moves := [], resigned := none, rev := 0 }

end Game

/-! ## Policy -/

/-- Participant-only visibility: the one rule every read and write is scoped
    by. Spectators or sharing would be a change to this definition. -/
def visible (p : PlayerId) (g : Game) : Bool := g.isParticipant p

/-! ## Specifications -/

/-- A stored game is valid. -/
structure Valid (g : Game) : Prop where
  distinct : g.x ≠ g.o
  nodup : (g.moves.map (·.i)).Nodup
  history : Rules.legalHistory g.moves = true
  length : g.moves.length ≤ 9
  rev : g.rev = g.moves.length + (if g.resigned.isSome then 1 else 0)
  resignedBy : ∀ p, g.resigned = some p → p = g.x ∨ p = g.o

/-- The resignation clause as a checkable condition. -/
def resignedOk (g : Game) : Bool :=
  match g.resigned with
  | some p => p == g.x || p == g.o
  | none => true

/-- `Valid`, as a Boolean check (run on every load and before every write). -/
def validB (g : Game) : Bool :=
  g.x != g.o && (g.moves.map (·.i)).Nodup && Rules.legalHistory g.moves &&
  decide (g.moves.length ≤ 9) &&
  g.rev == g.moves.length + (if g.resigned.isSome then 1 else 0) && resignedOk g

theorem validB_iff (g : Game) : validB g = true ↔ Valid g := by
  constructor
  · intro h
    simp only [validB, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
    refine ⟨h1, h2, h3, h4, h5, fun p hp => ?_⟩
    simp only [resignedOk, hp] at h6
    simpa using h6
  · intro v
    have h6 : resignedOk g = true := by
      unfold resignedOk
      cases hr : g.resigned with
      | none => rfl
      | some p => simpa using v.resignedBy p hr
    simp [validB, v.distinct, v.nodup, v.history, v.length, v.rev, h6]

instance (g : Game) : Decidable (Valid g) := decidable_of_iff _ (validB_iff g)

inductive Command where
  | play (expected : Revision) (cell : Cell)
  | resign
  deriving DecidableEq, Repr

/-- Who may attempt what. -/
def Allowed (p : PlayerId) (g : Game) : Command → Prop
  | .play _ _ => g.isParticipant p = true ∧ g.outcome = .ongoing ∧ g.toMove = p
  | .resign => g.isParticipant p = true

/-- What an accepted command does. -/
def Transition (p : PlayerId) (before : Game) : Command → Game → Prop
  | .play _ c, after => after = { before with moves := before.moves ++ [c], rev := before.rev + 1 }
  | .resign, after =>
      (before.resigned = some p ∧ after = before) ∨
      (before.outcome = .ongoing ∧ after = { before with resigned := some p, rev := before.rev + 1 })

/-! ## Decisions -/

inductive DomainError where
  | notParticipant
  | staleRevision (current : Revision)
  | gameOver
  | notYourTurn
  | cellTaken
  | selfPlay
  deriving DecidableEq, Repr

def playMove (p : PlayerId) (expected : Revision) (c : Cell) (g : Game) : Except DomainError Game :=
  if !g.isParticipant p then .error .notParticipant
  else if g.rev ≠ expected then .error (.staleRevision g.rev)
  else if g.outcome ≠ .ongoing then .error .gameOver
  else if g.toMove ≠ p then .error .notYourTurn
  else if !g.isFree c then .error .cellTaken
  else .ok { g with moves := g.moves ++ [c], rev := g.rev + 1 }

/-- Resigning twice is not an error: the second resignation returns the
    game unchanged (state idempotence). -/
def resign (p : PlayerId) (g : Game) : Except DomainError Game :=
  if !g.isParticipant p then .error .notParticipant
  else if g.resigned = some p then .ok g
  else if g.outcome ≠ .ongoing then .error .gameOver
  else .ok { g with resigned := some p, rev := g.rev + 1 }

def openGame (id : GameId) (p opponent : PlayerId) (tc : TimeControl) : Except DomainError Game :=
  if p = opponent then .error .selfPlay else .ok (Game.opened id p opponent tc)

def decide (p : PlayerId) (g : Game) : Command → Except DomainError Game
  | .play e c => playMove p e c g
  | .resign => resign p g

end PrivateGames
