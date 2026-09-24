/-
  The scoped repository (M4): the only data access proved operations get.

  * Reads of games take the actor and build a LeanDB `Pred` with the
    participant policy conjoined (`x = actor OR o = actor`), so the query
    itself never returns a row the actor cannot see. The Lean-side
    predicate (`visible`) is re-checked on the decoded row as well.
  * Loads re-validate (`reconstruct`); invalid rows are `.corrupt`.
  * Commits are compare-and-swap on the stored row (LeanDB `update`), inside
    one `BEGIN IMMEDIATE` transaction that also re-checks authority against
    the row being replaced and writes the retry receipt. A stale revision is
    `.conflict`; a lost authority is `.notFound`.
  * The raw `Conn` is not exported: `Repo` is a record of closures.

  Decision 0008 (Q5) records the snapshot and authority semantics.
-/
import PrivateGames.Storage.Schema
import PrivateGames.App.Core
import LeanApi.Runtime.Blocking
import LeanCrypto

namespace PrivateGames.Storage

open LeanDb

inductive RepoError where
  | notFound
  | conflict
  | corrupt (why : String)
  | keyReused
  | busy
  | db (why : String)
  deriving Repr, BEq, Inhabited

instance : ToString RepoError where
  toString
    | .notFound => "not found" | .conflict => "conflict" | .corrupt w => s!"corrupt: {w}"
    | .keyReused => "idempotency key reused with a different request" | .busy => "busy"
    | .db w => s!"database: {w}"

open PrivateGames.App (Receipt Keyed Write)

/-- The persistence contract handlers see. Every game read takes the actor. -/
structure Repo where
  /-- The game if it exists and `actor` participates; `none` otherwise
      (the two are indistinguishable by design). -/
  loadVisible : PlayerId → GameId → IO (Except RepoError (Option Game))
  /-- The actor's games in id order, with a window, and the total count of the
      same selection. -/
  listVisible : PlayerId → (offset limit : Nat) → IO (Except RepoError (List Game × Nat))
  /-- Look up a receipt for a keyed command. -/
  receipt : PlayerId → (op key : String) → IO (Except RepoError (Option Receipt))
  /-- Atomically: (1) if keyed and a receipt exists, return it (or
      `keyReused`); (2) apply the write (CAS against `old`, authority
      re-checked on the row); (3) record the receipt built from the written
      game. Returns the written game and the receipt. -/
  commit : PlayerId → Write → Option Keyed → (Game → LeanApi.Res) →
    IO (Except RepoError (LeanApi.Res × Bool))
  /-- Player / token management (not protected domain data). -/
  createPlayer : (name hash : String) → IO (Except RepoError PlayerId)
  playerByName : String → IO (Except RepoError (Option (PlayerId × String)))
  addToken : (digest : String) → PlayerId → IO (Except RepoError Unit)
  tokenPlayer : (digest : String) → IO (Except RepoError (Option PlayerId))
  playerExists : PlayerId → IO (Except RepoError Bool)

/-! ## The policy as a LeanDB predicate -/

/-- `x = actor OR o = actor`: pushed to SQL, so the query only returns
    visible rows. -/
def visiblePred (p : PlayerId) : Pred [GameRow] :=
  .or (.eq (.here GameRow.Field.x) .eq (pref p)) (.eq (.here GameRow.Field.o) .eq (pref p))

def gidRef (g : GameId) : LeanDb.Id GameRow := ⟨Int64.ofNat g.n⟩

private def dbErr : DbError → RepoError
  | .stale .. => .conflict
  | .notFound .. => .notFound
  | .duplicate .. => .conflict
  | e => .db (toString e)

/-- Load a visible game inside the current transaction (the id and the policy
    are both in the query). -/
def loadVisibleDb (p : PlayerId) (gid : GameId) : DbM (Except RepoError (Option (Stored GameRow × Game))) := do
  let pred : Pred [GameRow] := .and (.eq .id .eq (gidRef gid)) (visiblePred p)
  let rows ← selectP [GameRow] pred
  match rows[0]? with
  | none => return .ok none
  | some s =>
    match reconstruct s with
    | .error w => return .error (.corrupt w)
    | .ok g => return if visible p g then .ok (some (s, g)) else .ok none

def receiptDb (p : PlayerId) (op key : String) : DbM (Option (Stored ReceiptRow)) := do
  let pred : Pred [ReceiptRow] :=
    .and (.eq (.here ReceiptRow.Field.actor) .eq (pref p))
      (.and (.eq (.here ReceiptRow.Field.op) .eq op) (.eq (.here ReceiptRow.Field.key) .eq key))
  return (← selectP [ReceiptRow] pred)[0]?

inductive TxAbort where
  | err (e : RepoError)
  | replay (r : LeanApi.Res)

private def encodeHeaders (hs : List (String × String)) : String :=
  (Lean.Json.arr (hs.map fun (k, v) => Lean.Json.arr #[.str k, .str v]).toArray).compress

private def decodeHeaders (s : String) : List (String × String) :=
  match Lean.Json.parse s with
  | .ok (.arr xs) => xs.toList.filterMap fun
      | .arr #[.str k, .str v] => some (k, v)
      | _ => none
  | _ => []

/-- A receipt row stores the whole response: status, headers (JSON) and
    body (base64). The headers go in `fingerprint`'s sibling columns. -/
def receiptOfRow (r : ReceiptRow) : Receipt :=
  match r.body.splitOn "\n" with
  | [hs, b] => ⟨r.fingerprint, r.status, decodeHeaders hs, (LeanCrypto.Base64.decode b).getD .empty⟩
  | _ => ⟨r.fingerprint, r.status, [], .empty⟩

def rowBody (res : LeanApi.Res) : String :=
  encodeHeaders res.headers ++ "\n" ++ LeanCrypto.Base64.encode res.body

/-- The commit transaction body: replay check, write, receipt, atomically. -/
def commitDb (p : PlayerId) (w : Write) (keyed : Option Keyed) (build : Game → LeanApi.Res) :
    DbM (Except RepoError (LeanApi.Res × Bool)) := do
  let r ← LeanDb.transaction (ε := TxAbort) do
    -- (1) replay: a receipt committed by a concurrent or earlier request wins
    if let some k := keyed then
      if let some rc ← receiptDb p k.op k.key then
        if rc.val.fingerprint != k.fingerprint then return .abort (.err .keyReused)
        return .abort (.replay (receiptOfRow rc.val).toRes)
    -- (2) write
    let written ← match w with
      | .insertGame g =>
        if let .error why := Valid.stored.guardWrite g then pure (Except.error (RepoError.corrupt why)) else
        let s ← insert GameRow (GameRow.ofGame g)
        pure (.ok { g with id := ⟨s.id.toInt64.toNatClampNeg⟩ })
      | .updateGame old new =>
        if let .error why := Valid.stored.guardWrite new then pure (.error (RepoError.corrupt why)) else
        -- authority and revision re-checked against the row being replaced,
        -- under the write lock (BEGIN IMMEDIATE)
        match ← loadVisibleDb p old.id with
        | .error e => pure (.error e)
        | .ok none => pure (.error .notFound)
        | .ok (some (stored, cur)) =>
          if cur != old then pure (.error .conflict) else
          if new.x != old.x || new.o != old.o then
            pure (.error (.corrupt "a write may not change participants")) else
          let _ ← update stored (GameRow.ofGame new)
          pure (.ok new)
    match written with
    | .error e => return .abort (.err e)
    | .ok g =>
      let res := build g
      -- (3) receipt, in the same transaction
      if let some k := keyed then
        let _ ← insert ReceiptRow { actor := pref p, op := k.op, key := k.key,
                                    fingerprint := k.fingerprint, status := res.status, body := rowBody res }
      return .commit (res, false)
  match r with
  | .ok v => return .ok v
  | .error (.err e) => return .error e
  | .error (.replay rc) => return .ok (rc, true)

/-! ## Runtime: one writer, a pool of readers -/

structure Runtime where
  writer : LeanApi.Worker
  readers : LeanApi.Pool
  writeConn : Conn
  readConns : Array Conn

private def runDb (conn : Conn) (act : DbM α) : IO (Except RepoError α) := do
  match ← DbM.run conn act with
  | .ok a => return .ok a
  | .error e => return .error (dbErr e)

private def onWorker (w : LeanApi.Worker) (act : IO (Except RepoError α)) : IO (Except RepoError α) := do
  match ← w.run act with
  | .ok r => return r
  | .error .busy => return .error .busy
  | .error .stopped => return .error (.db "worker stopped")

private def flatten : Except RepoError (Except RepoError α) → Except RepoError α
  | .ok r => r
  | .error e => .error e

/-- Open `path` with one write connection (on a dedicated writer thread)
    and `readers` read-only connections (round-robin on reader threads). -/
def Runtime.open (path : System.FilePath) (readers : Nat := 4) (queue : Nat := 1024) : IO Runtime := do
  let writeConn ← match ← openDb path schema with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"open {path}: {e}")
  let mut rcs := #[]
  for _ in [0:max readers 1] do
    match ← openDbRaw path (readOnly := true) with
    | .ok c => rcs := rcs.push c
    | .error e => throw (IO.userError s!"open reader {path}: {e}")
  let writer ← LeanApi.Worker.start queue
  -- one worker per reader connection, so a connection is only ever used by one thread
  let workers ← rcs.mapM fun _ => LeanApi.Worker.start queue
  return { writer, readers := { workers, next := ← IO.mkRef 0 }, writeConn, readConns := rcs }

private def readOn (rt : Runtime) (act : DbM α) : IO (Except RepoError α) := do
  let i ← rt.readers.next.modifyGet fun i => (i, i + 1)
  let k := i % rt.readConns.size
  match rt.readers.workers[k]?, rt.readConns[k]? with
  | some w, some c => onWorker w (runDb c act)
  | _, _ => return .error (.db "no reader")

private def writeOn (rt : Runtime) (act : DbM α) : IO (Except RepoError α) :=
  onWorker rt.writer (runDb rt.writeConn act)

def Runtime.repo (rt : Runtime) : Repo where
  loadVisible p gid := do
    return flatten (← readOn rt do return (← loadVisibleDb p gid).map (·.map (·.2)))
  listVisible p off lim := do
    flatten <$> readOn rt (LeanDb.readSnapshot do
      let total ← countP (visiblePred p)
      let rows ← fetchFiltered GameRow (visiblePred p) (window := { limit := some lim, offset := off })
      let games := rows.toList.map reconstruct
      match games.mapM id with
      | .ok gs => return .ok (gs.filter (visible p), total)
      | .error w => return .error (.corrupt w))
  receipt p op key := do
    return (← readOn rt (receiptDb p op key)).map (·.map fun r => receiptOfRow r.val)
  commit p w keyed build := do
    flatten <$> writeOn rt (commitDb p w keyed build)
  createPlayer name hash := do
    match ← writeOn rt (insert PlayerRow { name, passwordHash := hash }) with
    | .ok s => return .ok (pid s.id)
    | .error e => return .error e
  playerByName name := do
    readOn rt do
      let rows ← selectP [PlayerRow] (.eq (.here PlayerRow.Field.name) .eq name)
      return rows[0]?.map fun s => (pid s.id, s.val.passwordHash)
  addToken digest p := do
    return (← writeOn rt (insert TokenRow { digest, player := pref p })).map fun _ => ()
  tokenPlayer digest := do
    readOn rt do
      let rows ← selectP [TokenRow] (.eq (.here TokenRow.Field.digest) .eq digest)
      return rows[0]?.map (pid ·.val.player)
  playerExists p := do
    readOn rt do return (← LeanDb.get (pref p)).isSome

def Runtime.close (rt : Runtime) : IO Unit := do
  rt.writer.stop
  rt.readers.stop

end PrivateGames.Storage
