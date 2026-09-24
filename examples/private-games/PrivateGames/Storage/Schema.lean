/-
  Persistence mapping (M4): domain values ↔ LeanDB entities.

  Column codecs are built from the same smart constructors the HTTP
  extractors use (decision 0006), so storage cannot hold a value the API
  would reject, and a row that fails validation is a typed decode error.

  Tables:
    player   name, password hash
    token    SHA-256 digest of an opaque bearer token → player (unique digest)
    game     x, o, minutes, resigned, rev, + child list game_moves(cell)
    receipt  (actor, op, key) unique → request fingerprint, status, body

  The raw `Conn` stays inside `PrivateGames.Storage`. Handlers get the
  scoped repository (`Repo.lean`) only.
-/
import LeanDb
import PrivateGames.Domain.Proofs

namespace PrivateGames.Storage

open LeanDb

/-! ## Column codecs from smart constructors -/

instance : ColCodec Cell := ColCodec.via (β := Nat) (·.i) Cell.make
instance : ColCodec TimeControl := ColCodec.via (β := Nat) (·.minutes) TimeControl.make

/-- The `Nat` column codec round-trips below 2^63 (SQLite INTEGER range). -/
theorem nat_roundtrip (n : Nat) (h : n < 2^63) :
    (ColCodec.fromCol (ColCodec.toCol n) : Except String Nat) = .ok n := by
  have h1 : ¬ (Int64.ofNat n < 0) := by
    rw [Int64.lt_iff_toInt_lt]; simp [Int64.toInt_ofNat_of_lt h]
  have hmax : LeanDb.natSqlMax = 2^63 - 1 := by decide
  have hs : LeanDb.natToSql n = some (Int64.ofNat n) := by
    simp only [LeanDb.natToSql, hmax]; split <;> first | rfl | omega
  simp [ColCodec.fromCol, ColCodec.toCol, hs, h1, Int64.toNatClampNeg_ofNat_of_lt h]

/-- Round-trip law for the cell codec: decode (encode c) = c. -/
theorem cell_roundtrip (c : Cell) : (ColCodec.fromCol (ColCodec.toCol c) : Except String Cell) = .ok c := by
  show (do Cell.make (← (ColCodec.fromCol (ColCodec.toCol c.i) : Except String Nat))) = .ok c
  rw [nat_roundtrip c.i (by have := c.isLt; omega)]
  exact Cell.make_i c

theorem timeControl_roundtrip (t : TimeControl) :
    (ColCodec.fromCol (ColCodec.toCol t) : Except String TimeControl) = .ok t := by
  show (do TimeControl.make (← (ColCodec.fromCol (ColCodec.toCol t.minutes) : Except String Nat))) = .ok t
  rw [nat_roundtrip t.minutes (by have := t.isValid; omega)]
  exact TimeControl.make_minutes t

/-! ## Entities -/

structure PlayerRow where
  name : String
  passwordHash : String
  deriving Repr, LeanDb.Entity

instance : LeanDb.Indexes PlayerRow := ⟨#[{ unique := true, columns := #["name"] }]⟩

structure TokenRow where
  digest : String
  player : Ref PlayerRow
  deriving Repr, LeanDb.Entity

instance : LeanDb.Indexes TokenRow := ⟨#[{ unique := true, columns := #["digest"] }]⟩

structure MoveRow where
  cell : Cell
  deriving Repr, LeanDb.Inline

structure GameRow where
  x : Ref PlayerRow
  o : Ref PlayerRow
  minutes : TimeControl
  resigned : Option (Ref PlayerRow)
  rev : Nat
  moves : List MoveRow
  deriving Repr, LeanDb.Entity

instance : LeanDb.Indexes GameRow :=
  ⟨#[{ columns := #["x"] }, { columns := #["o"] }]⟩

/-- A retry receipt: the recorded outcome of one keyed command. Written in
    the same transaction as the state change it describes. -/
structure ReceiptRow where
  actor : Ref PlayerRow
  op : String
  key : String
  /-- SHA-256 of the canonical request input; reuse with another input is refused. -/
  fingerprint : String
  status : Nat
  body : String
  deriving Repr, LeanDb.Entity

instance : LeanDb.Indexes ReceiptRow :=
  ⟨#[{ unique := true, columns := #["actor", "op", "key"] }]⟩

def schema : List TableSpec :=
  orderSpecs (Entity.specs PlayerRow ++ Entity.specs TokenRow ++ Entity.specs GameRow ++ Entity.specs ReceiptRow)

/-! ## Row ↔ domain -/

def pid (r : Ref PlayerRow) : PlayerId := ⟨r.toInt64.toNatClampNeg⟩
def pref (p : PlayerId) : Ref PlayerRow := ⟨Int64.ofNat p.n⟩

def GameRow.toGame (id : LeanDb.Id GameRow) (r : GameRow) : Game :=
  { id := ⟨id.toInt64.toNatClampNeg⟩, x := pid r.x, o := pid r.o, timeControl := r.minutes,
    moves := r.moves.map (·.cell), resigned := r.resigned.map pid, rev := r.rev }

def GameRow.ofGame (g : Game) : GameRow :=
  { x := pref g.x, o := pref g.o, minutes := g.timeControl, resigned := g.resigned.map pref,
    rev := g.rev, moves := g.moves.map (⟨·⟩) }

/-- Reconstruction re-validates: a stored game that is not `Valid` is a
    typed error, never a crash and never a game. -/
def reconstruct (s : Stored GameRow) : Except String Game :=
  let g := s.val.toGame s.id
  Valid.stored.guardLoad s!"stored game {g.id}" g

end PrivateGames.Storage
