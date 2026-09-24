/-
  private-games over LeanDB programs (LAPI-05).

  The five game routes as LeanDB programs over the `Games` schema:
  `listGames` and `readGame` are `Read`s, the writes are transactions
  (`Tx`). Their pure meaning is over `DbState Games`, and `DbApi.service`
  serves them from SQLite: one snapshot per read, one `BEGIN IMMEDIATE`
  transaction per write, authentication (a token lookup) inside it.

  The answers are the reference API's (`PrivateGames.Api`, over the
  in-memory `World`), byte for byte: the differential test runs the model,
  the reference API, the native service and this one on the same probes.

  Receipts: a keyed write looks its receipt up by the declared unique key
  (`ReceiptRow.byKey`) in the same transaction, replays it or refuses a
  reused key, and otherwise decides and records the answer with the
  change. A request that answers without writing (a repeated resignation)
  records nothing, as in the reference. The writer's `BEGIN IMMEDIATE`
  makes lookup-then-insert race-free.
-/
import PrivateGames.Api
import PrivateGames.App.Service
import LeanApi.Http.DbEndpoint

namespace PrivateGames.DbApi

open LeanApi Lean LeanDb PrivateGames PrivateGames.App PrivateGames.Storage
open PrivateGames.Api (IdemKey ETagRev KeyHeader OpenBody MoveBody PageReq GameView GamePage
  Replayed GameError)

/-! ## Actors -/

/-- A bearer token is a `TokenRow`, found by its digest. -/
def tokenPlayer (t : String) : Read Games (Option PlayerId) :=
  (·.map fun row => pid row.val.player) <$>
    Read.lookup TokenRow TokenRow.Unique.byDigest (Tokens.digest t)

instance gamesAuth : AuthenticatesDb Games PlayerId :=
  AuthenticatesDb.sessions tokenPlayer (realm := "games")

/-! ## The scoped query -/

/-- The games `p` plays in. -/
def GameRow.visibleTo (p : PlayerId) : LeanDb.Query Games [GameRow] (Stored GameRow) :=
  (LeanDb.Query.from GameRow).where' fun g => g.val.x == pref p || g.val.o == pref p

/-- The game with id `gid`, if `p` plays in it. -/
def visibleGame (p : PlayerId) (gid : GameId) : Read Games (Option (Stored GameRow)) :=
  Read.first ((GameRow.visibleTo p).where' fun g => g.id == gidRef gid)

def versioned (s : Stored GameRow) : Versioned GameView := PrivateGames.Api.Game.versioned (reconstruct s)

/-! ## Retries -/

/-- A keyed write: replay the recorded answer, refuse a reused key, or
    decide. `decide` says whether it wrote; a write is recorded with its
    answer, in the same transaction. -/
def keyed [ToResponse α] (me : PlayerId) (k? : Option Keyed)
    (decide : Txn σ Games GameError (Bool × α)) : Txn σ Games GameError (Replayed α) :=
  match k? with
  | none => do let (_, a) ← decide; pure (.fresh a)
  | some k => do
    match ← Txn.liftRead (Read.lookup ReceiptRow ReceiptRow.Unique.byKey (pref me, k.op, k.key)) with
    | some rc =>
      if rc.val.fingerprint == k.fingerprint then pure (.replay (receiptOfRow rc.val))
      else Txn.throw .keyReused
    | none =>
      let (wrote, a) ← decide
      if wrote then
        let res := ToResponse.toRes a
        let _ ← Txn.orAbort (Txn.insert ReceiptRow (Checked.of
            { actor := pref me, op := k.op, key := k.key, fingerprint := k.fingerprint,
              status := res.status, body := rowBody res } trivial)) fun
          | .duplicate .. => GameError.keyReused
          | .missingRef _ => GameError.hidden
      pure (.fresh a)

/-! ## Endpoints -/

/-- Open a game against `opponent`. -/
def openGame (me : Auth PlayerId) (body : Body OpenBody) (key : KeyHeader) :
    Tx Games GameError (Replayed (Created (Versioned GameView))) := fun _ =>
  keyed me.val (keyedFor .openGame (key.val.map (·.val)) s!"openGame|{body.val.opponent.n}|{body.val.tc.minutes}") do
    let opp := body.val.opponent
    let known ← Txn.liftRead (Read.get PlayerRow (pref opp))
    if known.isNone || opp.n ≥ 2^63 then Txn.throw .unknownOpponent
    match h : PrivateGames.openGame ⟨0⟩ me.val opp body.val.tc with
    | .error e => Txn.throw (.domain e)
    | .ok _ =>
      if hb : me.val.n < 2^63 ∧ opp.n < 2^63 then
        let row ← Txn.orAbort (Txn.insert GameRow (GameRow.checkedOpen h hb.1 hb.2)) fun
          | .missingRef _ => GameError.unknownOpponent
          | .duplicate ix _ => nomatch ix
        let g := reconstruct row.toStored
        pure (true, { val := PrivateGames.Api.Game.versioned g, location := some s!"/games/{g.id.n}" })
      else Txn.throw .unknownOpponent

/-- One page of my games, and how many there are, from one snapshot. -/
def listGames (me : Auth PlayerId) (q : LeanApi.Query PageReq) : Read Games GamePage := do
  let page ← Read.page (GameRow.visibleTo me.val)
    { offset := (q.val.page - 1) * q.val.per, limit := some q.val.per }
  pure ⟨page.items.map reconstruct, page.total, q.val.page, q.val.per⟩

/-- One of my games. Someone else's game is indistinguishable from a missing one. -/
def readGame (me : Auth PlayerId) (id : Path GameId) :
    Read Games (Except GameError (Versioned GameView)) := do
  match ← visibleGame me.val id.val with
  | some g => return .ok (versioned g)
  | none => return .error .hidden

/-- Write a decided transition of a stored game: validity of the new row
    from `decide_valid`, the row read in this transaction replaced by
    compare-and-swap. -/
def writeStep (me : PlayerId) (cmd : Command) (s : Stored GameRow) {g' : Game}
    (h : PrivateGames.decide me (reconstruct s) cmd = .ok g') : Txn σ Games GameError (Bool × Versioned GameView) :=
  if hv : GameRow.invariant s.val = true then do
    let _ ← Txn.orAbort (Txn.update GameRow s (GameRow.checkedStep s hv h)) fun
      | .stale _ | .gone | .missingRef _ => GameError.hidden
      | .duplicate ix _ => nomatch ix
    pure (true, PrivateGames.Api.Game.versioned g')
  else Txn.throw .hidden  -- unreachable: LeanDB refuses such a row when it is read

/-- Play a move in one of my games, decided against revision `rev`. -/
def playMove (me : Auth PlayerId) (rev : IfMatchRequired ETagRev) (body : Body MoveBody) (id : Path GameId)
    (key : KeyHeader) : Tx Games GameError (Replayed (Versioned GameView)) := fun _ =>
  keyed me.val (keyedFor .playMove (key.val.map (·.val)) s!"playMove|{id.val.n}|{rev.val.rev}|{body.val.cell.i}") do
    match ← Txn.liftRead (visibleGame me.val id.val) with
    | none => Txn.throw .hidden
    | some s =>
      match h : PrivateGames.decide me.val (reconstruct s) (.play rev.val.rev body.val.cell) with
      | .error .notParticipant => Txn.throw .hidden
      | .error e => Txn.throw (.domain e)
      | .ok _ => writeStep me.val _ s h

/-- Resign one of my games. Resigning twice answers the same game. -/
def resign (me : Auth PlayerId) (id : Path GameId) (key : KeyHeader) :
    Tx Games GameError (Replayed (Versioned GameView)) := fun _ =>
  keyed me.val (keyedFor .resign (key.val.map (·.val)) s!"resign|{id.val.n}") do
    match ← Txn.liftRead (visibleGame me.val id.val) with
    | none => Txn.throw .hidden
    | some s =>
      match h : PrivateGames.decide me.val (reconstruct s) .resign with
      | .error .notParticipant => Txn.throw .hidden
      | .error e => Txn.throw (.domain e)
      | .ok g' =>
        if g' == reconstruct s then pure (false, PrivateGames.Api.Game.versioned g')
        else writeStep me.val _ s h

/-! ## The HTTP surface -/

def gamesApi : DbApi Games := dbapi! [
  .post "/games"                       openGame,
  .get  "/games"                       listGames,
  .get  "/games/{id:nat}"              readGame,
  .post "/games/{id:nat}/moves"        playMove,
  .post "/games/{id:nat}/resignation"  resign
]

/-- The game routes from LeanDB programs, plus the (unproved) account
    routes, which touch only players and tokens. -/
def service (dc : DbConns) (repo : Repo) (dummy : String) (log : String → IO Unit := IO.eprintln)
    (params : LeanCrypto.Password.Params := {}) : Service :=
  Service.ofRouter (Router.build! (gamesApi.routes dc log ++ accountRoutes repo dummy params)) (stack log)

end PrivateGames.DbApi
