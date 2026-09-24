/-
  private-games as typed endpoints (docs/ENDPOINTS.md).

  The five game routes, each a pure function over the model `World` whose
  signature says what it takes, whether it changes state, and every way it
  answers. By the framework, `gamesApi.toSys` is a transition system, so the
  property library applies to it directly (`PrivateGames/ApiProofs.lean`):
  GET never changes state, and every stored game is valid with unique ids.

  The bodies call the domain (`openGame`, `playMove`, `resign`) and the same
  helpers as the reference model (`visibleGames`, `ownReceipts`,
  `recordReceipt`). The differential test checks that this API,
  the reference model and the native LeanDB service answer alike.
-/
import PrivateGames.Model.Isolation

namespace PrivateGames.Api

open LeanApi Lean PrivateGames PrivateGames.App PrivateGames.Model

/-! ## Actors -/

instance gamesAuth : Authenticates World PlayerId :=
  .sessions (fun w t => w.sessions.lookup (Tokens.digest t)) (realm := "games")

/-- What a player may see: `Model.SameView` (sessions, their visible games in
    order, their own receipts, player ids, the next id). -/
instance gamesView : ViewOf World PlayerId := ⟨SameView⟩

/-! ## Inputs -/


/-- The revision a move was decided against, sent as `If-Match: "<rev>"`. -/
structure ETagRev where
  rev : Revision

instance : FromParam ETagRev :=
  ⟨fun s => match s.toNat? with
    | some n => .ok ⟨n⟩
    | none => .error "expected an ETag \"<revision>\""⟩

/-- The `Idempotency-Key` and the retry identity the framework computes. -/
abbrev KeyHeader := Idempotency

/-- The framework's retry identity, in the core's shape. -/
def KeyHeader.keyed (k : KeyHeader) : Option Keyed := k.retry.map Keyed.ofRetry

structure OpenBody where
  opponent : PlayerId
  tc : TimeControl

instance : FromBody OpenBody := .record (OpenBody.mk <$> .req "opponent" <*> .dflt "minutes" TimeControl.default)

structure MoveBody where
  cell : Cell

instance : FromBody MoveBody := .record (MoveBody.mk <$> .req "cell")

/-- `?page&per`: `page ≥ 1`, `1 ≤ per ≤ 100`. -/
structure PageReq where
  page : Nat
  per : Nat

instance : FromQuery PageReq where
  fromQuery r := do
    let (page, per) ← both (Extract.queryD (α := Nat) "page" 1 r) (Extract.queryD (α := Nat) "per" 20 r)
    if page == 0 then .error [⟨"query.page", "must be at least 1"⟩]
    else if per == 0 || per > 100 then .error [⟨"query.per", "must be between 1 and 100"⟩]
    else .ok ⟨page, per⟩

/-! ## Outputs -/

/-- A game, as players see it. -/
structure GameView where
  game : Game

instance : ToJson GameView := ⟨fun v => gameJson v.game⟩

def Game.versioned (g : Game) : Versioned GameView := ⟨⟨g⟩, g.rev⟩

/-- One page of my games. -/
structure GamePage where
  items : List Game
  total : Nat
  page : Nat
  per : Nat

instance : ToResponse GamePage where
  toRes p := Res.json (Json.mkObj [("items", Json.arr (p.items.map gameJson).toArray),
    ("total", Json.num p.total), ("page", Json.num p.page), ("per", Json.num p.per)])

/-- A keyed write: freshly decided, or the recorded answer replayed. -/
inductive Replayed (α : Type) where
  | fresh (a : α)
  | replay (rc : Receipt)

instance [ToResponse α] : ToResponse (Replayed α) where
  toRes
    | .fresh a => ToResponse.toRes a
    | .replay rc => rc.toRes

/-- Every way a game request can be refused. -/
inductive GameError where
  /-- Not a game of mine, or no such game: the same answer (404). -/
  | hidden
  | domain (e : DomainError)
  | unknownOpponent
  | keyReused

instance : ToProblem GameError where
  status
    | .hidden => ⟨404, by decide⟩
    | .domain (.staleRevision _) => ⟨412, by decide⟩
    | .domain .notParticipant => ⟨404, by decide⟩
    | .domain .gameOver | .domain .notYourTurn | .domain .cellTaken => ⟨409, by decide⟩
    | .domain .selfPlay | .unknownOpponent | .keyReused => ⟨422, by decide⟩
  detail
    | .hidden | .domain .notParticipant => none
    | .domain (.staleRevision _) => some "the game has changed"
    | .domain .gameOver => some "the game is over"
    | .domain .notYourTurn => some "not your turn"
    | .domain .cellTaken => some "cell already taken"
    | .domain .selfPlay | .unknownOpponent => some "request validation failed"
    | .keyReused => some "Idempotency-Key was already used with a different request"
  extensions
    | .domain (.staleRevision cur) => [("rev", Json.num cur)]
    | .domain .gameOver => [("code", .str "game_over")]
    | .domain .notYourTurn => [("code", .str "not_your_turn")]
    | .domain .cellTaken => [("code", .str "cell_taken")]
    | .domain .selfPlay => [("errors", Json.arr #[FieldError.toJson ⟨"body.opponent", "cannot play yourself"⟩])]
    | .unknownOpponent => [("errors", Json.arr #[FieldError.toJson ⟨"body.opponent", "unknown player"⟩])]
    | _ => []

/-! ## Retries -/

/-- My receipt for `(op, key)`, if any. -/
def receiptOf (me : PlayerId) (w : World) (k : Keyed) : Option Receipt :=
  ((ownReceipts me w).find? fun (x, _) => x.op = k.op ∧ x.key = k.key).map (·.2)

/-- What a decision does: refuse, answer without changing anything, or
    change the store and answer. -/
inductive Decided (α : Type) where
  | refuse (e : GameError)
  | answer (a : α)
  | write (w : World) (a : α)

/-- The answer of a decision, without the new store. -/
def Decided.result : Decided α → Except GameError α
  | .refuse e => .error e
  | .answer a => .ok a
  | .write _ a => .ok a

/-- A keyed write: replay the recorded answer, refuse a reused key, or
    decide. A write is recorded with its answer, in the same step. -/
def keyed [ToResponse α] (me : PlayerId) (k? : Option Keyed)
    (decide : World → Decided α) : Writes World (Except GameError (Replayed α)) := fun w =>
  match k?.bind fun k => (receiptOf me w k).map (k, ·) with
  | some (k, rc) => (w, if rc.fingerprint == k.fingerprint then .ok (.replay rc) else .error .keyReused)
  | none =>
    match decide w with
    | .refuse e => (w, .error e)
    | .answer a => (w, .ok (.fresh a))
    | .write w' a => (recordReceipt me k? (ToResponse.toRes a) w', .ok (.fresh a))

/-! ## Endpoints -/

/-- Open a game against `opponent`. -/
def openGame (me : Auth PlayerId) (body : Body OpenBody) (key : KeyHeader) :
    Writes World (Except GameError (Replayed (Created (Versioned GameView)))) :=
  keyed me.val key.keyed
    fun w =>
      if !w.players.contains body.val.opponent then .refuse .unknownOpponent else
      match PrivateGames.openGame ⟨w.nextGame⟩ me.val body.val.opponent body.val.tc with
      | .error e => .refuse (.domain e)
      | .ok g => .write { w with games := w.games ++ [g], nextGame := w.nextGame + 1 }
                  { val := Game.versioned g, location := some s!"/games/{g.id.n}" }

/-- One page of my games. -/
def listGames (me : Auth PlayerId) (q : QueryParams PageReq) : Reads World GamePage := fun w =>
  let vs := visibleGames me.val w
  ⟨(vs.drop ((q.val.page - 1) * q.val.per)).take q.val.per, vs.length, q.val.page, q.val.per⟩

/-- One of my games. Someone else's game is indistinguishable from a missing one. -/
def readGame (me : Auth PlayerId) (id : Path GameId) : Reads World (Except GameError (Versioned GameView)) :=
  fun w => match (visibleGames me.val w).find? (·.id = id.val) with
    | some g => .ok (Game.versioned g)
    | none => .error .hidden

/-- Replace `old` by `new` in the store. -/
def replaceGame (w : World) (old new : Game) : World :=
  { w with games := w.games.map fun g => if g = old then new else g }

/-- Play a move in one of my games, decided against revision `rev`. -/
def playMove (me : Auth PlayerId) (rev : IfMatchRequired ETagRev) (body : Body MoveBody) (id : Path GameId)
    (key : KeyHeader) : Writes World (Except GameError (Replayed (Versioned GameView))) :=
  keyed me.val key.keyed
    fun w =>
      match (visibleGames me.val w).find? (·.id = id.val) with
      | none => .refuse .hidden
      | some g =>
        match PrivateGames.playMove me.val rev.val.rev body.val.cell g with
        | .error .notParticipant => .refuse .hidden
        | .error e => .refuse (.domain e)
        | .ok g' => .write (replaceGame w g g') (Game.versioned g')

/-- Resign one of my games. Resigning twice answers the same game. -/
def resign (me : Auth PlayerId) (id : Path GameId) (key : KeyHeader) :
    Writes World (Except GameError (Replayed (Versioned GameView))) :=
  keyed me.val key.keyed
    fun w =>
      match (visibleGames me.val w).find? (·.id = id.val) with
      | none => .refuse .hidden
      | some g =>
        match PrivateGames.resign me.val g with
        | .error .notParticipant => .refuse .hidden
        | .error e => .refuse (.domain e)
        | .ok g' => if g' == g then .answer (Game.versioned g) else .write (replaceGame w g g') (Game.versioned g')

/-! ## The HTTP surface -/

def gamesApi : Api World := api! [
  .post "/games"                       openGame,
  .get  "/games"                       listGames,
  .get  "/games/{id:nat}"              readGame,
  .post "/games/{id:nat}/moves"        playMove,
  .post "/games/{id:nat}/resignation"  resign
]

end PrivateGames.Api
