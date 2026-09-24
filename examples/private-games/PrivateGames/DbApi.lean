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
open PrivateGames.Api (ETagRev OpenBody MoveBody PageReq GameView GamePage
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
def GameRow.visibleTo (p : PlayerId) : Query Games [GameRow] (Stored GameRow) :=
  (Query.from GameRow).where' fun g => g.val.x == pref p || g.val.o == pref p

/-- The game with id `gid`, if `p` plays in it. -/
def visibleGame (p : PlayerId) (gid : GameId) : Read Games (Option (Stored GameRow)) :=
  Read.first ((GameRow.visibleTo p).where' fun g => g.id == gidRef gid)

def versioned (s : Stored GameRow) : Versioned GameView := PrivateGames.Api.Game.versioned (reconstruct s)

/-! ## Retries

The fingerprint is the framework's (`LeanApi.Retry`). Receipts stored
before that change carry the app's old operation name and fingerprint; they
still replay, because the app registers its old function as `v0`. -/

instance : LegacyFingerprint (DbState Games) := ⟨legacyV0⟩


/-- My receipt for this key, with the fingerprint to compare it against.
    Falls back to the pre-`v1` identity (`v0`) for receipts stored before
    the framework computed fingerprints. -/
def findReceipt (me : PlayerId) (k : Retry) : Txn σ Games GameError (Option (Stored ReceiptRow × String)) := do
  let receipt (op : String) := Txn.liftRead (Read.lookup ReceiptRow ReceiptRow.Unique.byKey (pref me, op, k.key))
  match ← receipt k.op with
  | some rc => pure (some (rc, k.fingerprint))
  | none => match k.legacy with
    | some (op0, fp0) => (·.map (·, fp0)) <$> receipt op0
    | none => pure none

/-- A keyed write: replay the recorded answer, refuse a reused key, or
    decide. The key and its fingerprint are the framework's. -/
def keyed [ToResponse α] (me : PlayerId) (key : Idempotency)
    (decide : Txn σ Games GameError (Bool × α)) : Txn σ Games GameError (Replayed α) :=
  match key.retry with
  | none => do let (_, a) ← decide; pure (.fresh a)
  | some k => do
    match ← findReceipt me k with
    | some (rc, fp) =>
      if rc.val.fingerprint == fp then pure (.replay (receiptOfRow rc.val))
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
def openGame (me : Auth PlayerId) (body : Body OpenBody) (key : Idempotency) :
    Tx Games GameError (Replayed (Created (Versioned GameView))) :=
  keyed me.val key do
    let opp := body.val.opponent
    if (← Txn.liftRead (Read.get PlayerRow (pref opp))).isNone then Txn.throw .unknownOpponent
    match h : PrivateGames.openGame ⟨0⟩ me.val opp body.val.tc with
    | .error e => Txn.throw (.domain e)
    | .ok _ =>
      let row ← Txn.orAbort (Txn.insert GameRow (GameRow.checkedOpen h)) fun
        | .missingRef _ => GameError.unknownOpponent
        | .duplicate ix _ => nomatch ix
      let g := reconstruct row.toStored
      pure (true, { val := PrivateGames.Api.Game.versioned g, location := some s!"/games/{g.id.n}" })

/-- One page of my games, and how many there are, from one snapshot. -/
def listGames (me : Auth PlayerId) (q : QueryParams PageReq) : Read Games GamePage := do
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
    (key : Idempotency) : Tx Games GameError (Replayed (Versioned GameView)) :=
  keyed me.val key do
    match ← Txn.liftRead (visibleGame me.val id.val) with
    | none => Txn.throw .hidden
    | some s =>
      match h : PrivateGames.decide me.val (reconstruct s) (.play rev.val.rev body.val.cell) with
      | .error .notParticipant => Txn.throw .hidden
      | .error e => Txn.throw (.domain e)
      | .ok _ => writeStep me.val _ s h

/-- Resign one of my games. Resigning twice answers the same game. -/
def resign (me : Auth PlayerId) (id : Path GameId) (key : Idempotency) :
    Tx Games GameError (Replayed (Versioned GameView)) :=
  keyed me.val key do
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

def gamesApi : DbApi Games := api! [
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
