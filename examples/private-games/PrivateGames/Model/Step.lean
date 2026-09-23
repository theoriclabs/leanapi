/-
  The reference model (M6): `step : Req → World → Res × World` for the
  exported proved routes.

  It covers every modeled branch: route miss / 405 / OPTIONS / redirects
  (shared `resolveIn`), authentication failure, decode failure, policy
  denial, conflicts, replays, and success. It calls the SAME `decode` and
  `core` as the native service (App/Core.lean). What differs is only the
  shell: the model reads `World` directly through `viewOf`, the native
  service reads LeanDB through the scoped repository.

  Scope: one request at a time (sequential). Concurrency is handled by the
  native commit (single writer + CAS) and is checked by tests, not proved.
-/
import PrivateGames.App.Core

namespace PrivateGames.Model

open LeanApi PrivateGames.App

structure ReceiptKey where
  actor : PlayerId
  op : String
  key : String
  deriving DecidableEq, Repr

structure World where
  games : List Game
  /-- token digest ↦ player -/
  sessions : List (String × PlayerId)
  players : List PlayerId
  receipts : List (ReceiptKey × Receipt)
  /-- The next id `insertGame` assigns. -/
  nextGame : Nat

/-! ## The actor's view: all a proved operation may observe -/

/-- Games visible to `p`, in id order as stored. -/
def visibleGames (p : PlayerId) (w : World) : List Game := w.games.filter (visible p)

/-- `p`'s own receipts. -/
def ownReceipts (p : PlayerId) (w : World) : List (ReceiptKey × Receipt) :=
  w.receipts.filter (·.1.actor = p)

/-- The scoped load: the model counterpart of the repository. It reads only
    `visibleGames`, `ownReceipts`, and player existence. -/
def load (p : PlayerId) (w : World) (n : Need) : Slice :=
  let vs := visibleGames p w
  { game := n.game.bind fun gid => vs.find? (·.id = gid)
    page := match n.page with
      | some (off, lim) => ((vs.drop off).take lim, vs.length)
      | none => ([], 0)
    receipt := n.receipt.bind fun (op, key) =>
      ((ownReceipts p w).find? fun (k, _) => k.op = op ∧ k.key = key).map (·.2)
    playerExists := match n.player with
      | some q => w.players.contains q
      | none => false }

/-! ## Commit -/

def recordReceipt (p : PlayerId) (k : Option Keyed) (res : Res) (w : World) : World :=
  match k with
  | none => w
  | some k => { w with receipts := w.receipts ++ [(⟨p, k.op, k.key⟩, Receipt.ofRes k.fingerprint res)] }

/-- The commit guard, identical to the native transaction's checks: the
    replaced game is still exactly what was decided on and visible to the
    actor, the new game is valid, and a write never changes participants. -/
def commitOk (p : PlayerId) (old new : Game) (w : World) : Bool :=
  (visibleGames p w).contains old && validB new && new.x == old.x && new.o == old.o

/-- The model commit: the same checks the native transaction makes. -/
def commit (p : PlayerId) (wr : Write) (k : Option Keyed) (build : Game → Res) (w : World) : Res × World :=
  match wr with
  | .insertGame g =>
    let g := { g with id := ⟨w.nextGame⟩ }
    let res := build g
    (res, recordReceipt p k res { w with games := w.games ++ [g], nextGame := w.nextGame + 1 })
  | .updateGame old new =>
    -- authority and revision re-checked on the row being replaced
    if commitOk p old new w then
      let res := build new
      (res, recordReceipt p k res { w with games := w.games.map fun g => if g = old then new else g })
    else (hidden, w)

def runPlan (p : PlayerId) : Plan → World → Res × World
  | .respond r, w => (r, w)
  | .write wr k build, w => commit p wr k build w

/-! ## The step function -/

def authenticate (r : Req) (w : World) : Except Res PlayerId :=
  match authDigest r with
  | .error res => .error res
  | .ok d => match w.sessions.lookup d with
    | some p => .ok p
    | none => .error unknownToken

/-- The operation, once routed. -/
def operate (op : Op) (r : Req) (w : World) : Res × World :=
  match authenticate r w with
  | .error res => (res, w)
  | .ok p =>
    match decode op r with
    | .error res => (res, w)
    | .ok i => runPlan p (core p i (load p w i.need)) w

def step (r : Req) (w : World) : Res × World :=
  match Router.resolveIn entries .redirect r with
  | .respond res => (res, w)
  | .route op ps => operate op { r with params := ps } w

end PrivateGames.Model
