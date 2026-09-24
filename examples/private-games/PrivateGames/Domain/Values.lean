/-
  Values of the private-games domain. No HTTP, no SQL.

  Decision 0006 (Q2): small bounded numbers carry a proof field
  (`Cell`, `TimeControl`): the bound is decidable, costs nothing to check,
  and proofs can use it directly. Identities are plain newtypes: possessing
  a well-formed id grants nothing. Every value has one smart constructor
  (`make`), and the HTTP extractors and LeanDB codecs both go through it.
-/
namespace PrivateGames

/-- A player id. It fits in a LeanDB `Ref` (below 2^63): the bound is part of
    the type, so storage never re-checks it (LAPI-12). -/
structure PlayerId where
  n : Nat
  lt : n < 2^63 := by decide
  deriving DecidableEq, Repr, Hashable, Ord

instance : Inhabited PlayerId := ⟨⟨0, by decide⟩⟩

/-- Another id than `p`, and than `p.other`: shifts by one, wrapping below
    2^63, so it is always distinct from `p` (used by the model's witnesses). -/
def PlayerId.next (p : PlayerId) : PlayerId :=
  if h : p.n + 1 < 2^63 then ⟨p.n + 1, h⟩ else ⟨0, by decide⟩

theorem PlayerId.next_n (p : PlayerId) : p.next.n = (p.n + 1) % 2^63 := by
  have := p.lt
  unfold PlayerId.next; split
  · simp; omega
  · simp; omega

theorem PlayerId.next_ne (p : PlayerId) : p.next ≠ p := by
  intro h; have e := congrArg PlayerId.n h; rw [PlayerId.next_n] at e; have := p.lt; omega

theorem PlayerId.next_next_ne (p : PlayerId) : p.next.next ≠ p := by
  intro h; have e := congrArg PlayerId.n h; rw [PlayerId.next_n, PlayerId.next_n] at e
  have := p.lt; omega

/-- An id from a number known to be in range (tests, ids read back from a
    trusted source). Out of range is a programming error: it becomes 0,
    which no player has. -/
def PlayerId.ofNat! (n : Nat) : PlayerId :=
  if h : n < 2^63 then ⟨n, h⟩ else ⟨0, by decide⟩

/-- A literal id; its bound is checked when it is written. -/
@[reducible] def PlayerId.lit (n : Nat) (h : n < 2^63 := by decide) : PlayerId := ⟨n, h⟩

structure GameId where
  n : Nat
  deriving DecidableEq, Repr, Hashable, Ord, Inhabited

instance : ToString PlayerId := ⟨fun p => toString p.n⟩
instance : ToString GameId := ⟨fun g => toString g.n⟩

def PlayerId.make (n : Nat) : Except String PlayerId :=
  if h : n == 0 || n >= 2^63 then .error "player id must be between 1 and 2^63-1"
  else .ok ⟨n, by simp at h; omega⟩

def GameId.make (n : Nat) : Except String GameId :=
  if n == 0 || n >= 2^63 then .error "game id must be between 1 and 2^63-1" else .ok ⟨n⟩

/-- A square of the 3×3 board, numbered 0–8 row by row. -/
structure Cell where
  i : Nat
  isLt : i < 9
  deriving DecidableEq, Repr

def Cell.make (n : Nat) : Except String Cell :=
  if h : n < 9 then .ok ⟨n, h⟩ else .error "cell must be between 0 and 8"

/-- Minutes per side: 1 to 180. Stored and shown; this slice has no clocks. -/
structure TimeControl where
  minutes : Nat
  isValid : 1 ≤ minutes ∧ minutes ≤ 180
  deriving DecidableEq, Repr

def TimeControl.make (m : Nat) : Except String TimeControl :=
  if h : 1 ≤ m ∧ m ≤ 180 then .ok ⟨m, h⟩ else .error "minutes must be between 1 and 180"

def TimeControl.default : TimeControl := ⟨10, by decide⟩

/-- The game's revision: bumped by every accepted transition. -/
abbrev Revision := Nat

theorem Cell.make_ok {n : Nat} {c : Cell} (h : Cell.make n = .ok c) : c.i = n := by
  unfold Cell.make at h; split at h <;> simp_all; cases h; rfl

theorem Cell.make_i (c : Cell) : Cell.make c.i = .ok c := by
  unfold Cell.make; simp [c.isLt]

theorem TimeControl.make_minutes (t : TimeControl) : TimeControl.make t.minutes = .ok t := by
  unfold TimeControl.make; simp [t.isValid]

theorem GameId.make_n (g : GameId) (h : g.n ≠ 0) (hb : g.n < 2^63) :
    GameId.make g.n = .ok g := by
  unfold GameId.make
  simp [h, Nat.not_le_of_gt hb]

end PrivateGames
