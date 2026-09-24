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

structure TokenRow where
  digest : String
  player : Ref PlayerRow
  deriving Repr, LeanDb.Entity

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
  deriving Repr

/-! ## Row ↔ domain -/

def pid (r : Ref PlayerRow) : PlayerId :=
  ⟨r.toInt64.toNatClampNeg, by have := r.toInt64.toNatClampNeg_lt; omega⟩
def pref (p : PlayerId) : Ref PlayerRow := ⟨Int64.ofNat p.n⟩

def GameRow.toGame (id : LeanDb.Id GameRow) (r : GameRow) : Game :=
  { id := ⟨id.toInt64.toNatClampNeg⟩, x := pid r.x, o := pid r.o, timeControl := r.minutes,
    moves := r.moves.map (·.cell), resigned := r.resigned.map pid, rev := r.rev }

def GameRow.ofGame (g : Game) : GameRow :=
  { x := pref g.x, o := pref g.o, minutes := g.timeControl, resigned := g.resigned.map pref,
    rev := g.rev, moves := g.moves.map (⟨·⟩) }

/-- The stored game invariant is the domain's `Valid`, through the row
    mapping (LAPI-04). LeanDB checks it on every read and every write
    (LDB-16), which replaces the repository's own `guardLoad`/`guardWrite`.
    The id is irrelevant (`GameRow.valid_id_irrel`). -/
@[leandb_invariant]
def GameRow.invariant (r : GameRow) : Bool := Valid.holdsB (r.toGame ⟨0⟩)

deriving instance LeanDb.Entity for GameRow

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

/-! ## Unique indexes and the schema (LeanDB M14 typed symbols)

Each `unique%` generates a constructor of `Unique α` whose key type is
the indexed columns' types, and the SQLite unique index. Non-unique
indexes (`GameRow`'s) stay `Indexes` entries: they never appear in a
failure type. `GameRow` declares no unique index, so `Unique GameRow` is
empty and a duplicate insert of a game cannot be stated. -/

unique% PlayerRow.byName := name
unique% TokenRow.byDigest := digest
unique% ReceiptRow.byKey := (actor, op, key)

schema% Games := PlayerRow, TokenRow, GameRow, ReceiptRow

def schema : List TableSpec :=
  orderSpecs (Entity.specs PlayerRow ++ Entity.specs TokenRow ++ Entity.specs GameRow ++ Entity.specs ReceiptRow)

/-! ## Migration from the v1 schema

Before LAPI-04 the unique indexes were unnamed (`uq_player_row_name`, …)
and `game_row` declared no invariant. Declaring them renames the three
unique indexes (same columns) and records the invariant, so the
fingerprint moves. `schemaV1` is that schema, reconstructed; a test pins
its fingerprint to the one deployed instances carry. The move is
non-destructive: add and drop index, restamp invariant. -/

def schemaV1 : List TableSpec :=
  schema.map fun t =>
    { t with «invariant» := none, indexes := t.indexes.map ({ · with name := none }) }

/-- The fingerprint every pre-LAPI-04 instance carries. -/
def schemaV1Fingerprint : String := "3475301517420757831"

/-! ## The invariant, proved against the domain -/

/-- `Valid` does not look at the id. -/
theorem GameRow.valid_id_irrel (r : GameRow) (i j : LeanDb.Id GameRow) :
    Valid (r.toGame i) ↔ Valid (r.toGame j) :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩, fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩⟩

/-- LeanDB's check on a row is exactly `Valid` of the game it maps to. -/
theorem GameRow.invariant_iff (r : GameRow) (i : LeanDb.Id GameRow) :
    GameRow.invariant r = true ↔ Valid (r.toGame i) :=
  (Valid.holdsB_iff _).trans (GameRow.valid_id_irrel r _ i)

/-- LeanDB's `Invariant GameRow` is the same statement. -/
theorem GameRow.Invariant_iff (r : GameRow) (i : LeanDb.Id GameRow) :
    LeanDb.Invariant GameRow r ↔ Valid (r.toGame i) := by
  show GameRow.invariant r = true ↔ _
  exact GameRow.invariant_iff r i

/-! ## `Checked GameRow` from domain proofs

A player id round-trips through a `Ref` only below 2^63, and `Valid`'s
`distinct` field needs that. `PlayerId` carries the bound (LAPI-12), so
every game's participants are in range by their type: no runtime check. -/

/-- Both participants are ids a `Ref` can carry: true of every game, by
    `PlayerId.lt`. -/
def _root_.PrivateGames.Game.Bounded (g : Game) : Prop := g.x.n < 2^63 ∧ g.o.n < 2^63

theorem _root_.PrivateGames.Game.bounded (g : Game) : g.Bounded := ⟨g.x.lt, g.o.lt⟩

theorem pid_lt (r : Ref PlayerRow) : (pid r).n < 2^63 := (pid r).lt

/-- `pid` and `pref` are exact inverses on player ids. -/
theorem pid_pref (p : PlayerId) : pid (pref p) = p := by
  cases p with
  | mk n h => simp [pid, pref, Int64.toNatClampNeg_ofNat_of_lt h]

theorem GameRow.toGame_bounded (r : GameRow) (i : LeanDb.Id GameRow) : (r.toGame i).Bounded :=
  ⟨pid_lt _, pid_lt _⟩

private theorem cells_roundtrip (ms : List Cell) :
    (ms.map (fun c => (⟨c⟩ : MoveRow))).map (·.cell) = ms := by
  induction ms <;> simp_all

private theorem cell_comp : (fun x : MoveRow => x.cell) ∘ (fun c => (⟨c⟩ : MoveRow)) = id := rfl

/-- A valid game with in-range participants stores as a row satisfying
    the invariant. -/
theorem GameRow.ofGame_invariant (g : Game) (hv : Valid g) (hb : g.Bounded) :
    LeanDb.Invariant GameRow (GameRow.ofGame g) := by
  rw [GameRow.Invariant_iff _ ⟨0⟩]
  have hx := pid_pref g.x
  have ho := pid_pref g.o
  have hres : (g.resigned.map pref).map pid = g.resigned := by
    cases hr : g.resigned with
    | none => rfl
    | some p =>
      rcases hv.resignedBy p hr with rfl | rfl
      · simp [hx]
      · simp [ho]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [GameRow.toGame, GameRow.ofGame, hx, ho, hres, cells_roundtrip]
  · exact hv.distinct
  · exact hv.nodup
  · exact hv.history
  · exact hv.length
  · exact hv.rev
  · exact hv.resignedBy

/-- The row mapping is a section on valid, in-range games. -/
theorem GameRow.toGame_ofGame (g : Game) (hv : Valid g) (hb : g.Bounded) (hid : g.id.n < 2^63) :
    (GameRow.ofGame g).toGame ⟨Int64.ofNat g.id.n⟩ = g := by
  have hx := pid_pref g.x
  have ho := pid_pref g.o
  have hres : (g.resigned.map pref).map pid = g.resigned := by
    cases hr : g.resigned with
    | none => rfl
    | some p =>
      rcases hv.resignedBy p hr with rfl | rfl
      · simp [hx]
      · simp [ho]
  cases g
  simp_all [GameRow.toGame, GameRow.ofGame, cell_comp, Int64.toNatClampNeg_ofNat_of_lt hid]

/-- A checked row from a valid, in-range game. No runtime check. -/
def GameRow.checked (g : Game) (hv : Valid g) (hb : g.Bounded) : Checked GameRow :=
  Checked.of (GameRow.ofGame g) (GameRow.ofGame_invariant g hv hb)

/-- Opening a game: validity from `Valid.preserved_openGame`. -/
def GameRow.checkedOpen {id : GameId} {p o : PlayerId} {tc : TimeControl} {g : Game}
    (h : openGame id p o tc = .ok g) : Checked GameRow :=
  GameRow.checked g (Valid.preserved_openGame id p o tc g h) g.bounded

theorem decide_participants {p : PlayerId} {g g' : Game} {cmd : Command}
    (h : PrivateGames.decide p g cmd = .ok g') : g'.x = g.x ∧ g'.o = g.o := by
  cases cmd with
  | play e c =>
    simp only [PrivateGames.decide, playMove] at h
    split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    split at h; · simp at h
    cases h; exact ⟨rfl, rfl⟩
  | resign =>
    simp only [PrivateGames.decide, resign] at h
    split at h; · simp at h
    split at h; · cases h; exact ⟨rfl, rfl⟩
    split at h; · simp at h
    cases h; exact ⟨rfl, rfl⟩

/-- A move or a resignation on a stored game: validity from
    `decide_valid` on the stored row's invariant, and the participants
    (hence the bound) carried over from the row. -/
def GameRow.checkedStep {p : PlayerId} {cmd : Command} {g' : Game} (s : Stored GameRow)
    (hs : LeanDb.Invariant GameRow s.val)
    (h : PrivateGames.decide p (s.val.toGame s.id) cmd = .ok g') : Checked GameRow :=
  GameRow.checked g' (decide_valid ((GameRow.Invariant_iff _ s.id).mp hs) h) g'.bounded

/-- The game a stored row maps to. LeanDB refuses a row that fails the
    invariant before it gets here (`.invariant`, 500 without detail). -/
def reconstruct (s : Stored GameRow) : Game := s.val.toGame s.id

end PrivateGames.Storage
