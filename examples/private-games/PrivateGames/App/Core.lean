/-
  The proved operations, as pure code shared by the native service and the
  reference model (decision 0005).

  Per request, after routing and authentication:
    decode : Op → Req → Except Res Input        (pure: path, query, headers, body)
    need   : Input → Need                       (what to load)
    core   : PlayerId → Input → Slice → Plan    (the decision; calls the domain)
  The shell loads the `Slice` for the `Need` through the scoped repository
  (native) or from the actor's `View` (model), and executes the `Plan`.

  Routes (DESIGN §9.2):
    POST /games                      OpenGame   {"opponent", "minutes"?}   Idempotency-Key?
    GET  /games?page&per             ListMyGames
    GET  /games/{id}                 ReadGame   → ETag
    POST /games/{id}/moves           PlayMove   {"cell"}  If-Match: "<rev>"  Idempotency-Key?
    POST /games/{id}/resignation     Resign     Idempotency-Key?
-/
import LeanApi
import PrivateGames.Domain.Proofs

namespace PrivateGames.App

open LeanApi Lean

/-! ## Plan vocabulary (shared with storage) -/

structure Receipt where
  fingerprint : String
  status : Nat
  headers : List (String × String)
  body : ByteArray

instance : Inhabited Receipt := ⟨⟨"", 0, [], .empty⟩⟩

def replayHeader : String × String := ("idempotent-replayed", "true")

/-- A replayed response: the recorded one, marked. -/
def markReplay (r : Res) : Res := r.setHeader replayHeader.1 replayHeader.2

def Receipt.ofRes (fp : String) (r : Res) : Receipt := ⟨fp, r.status, r.headers, r.body⟩
def Receipt.toRes (rc : Receipt) : Res := markReplay { status := rc.status, headers := rc.headers, body := rc.body }

/-- A keyed request's retry identity, as the framework computes it
    (`LeanApi.Retry`): the endpoint, the key, and the fingerprint of the
    request as the endpoint reads it. The app never builds one. -/
structure Keyed where
  op : String
  key : String
  fingerprint : String
  deriving Repr, BEq

def Keyed.ofRetry (r : Retry) : Keyed := ⟨r.op, r.key, r.fingerprint⟩

inductive Write where
  | insertGame (g : Game)
  | updateGame (old new : Game)
  deriving Repr

inductive Plan where
  | respond (res : Res)
  /-- Commit `w` (atomically with a receipt when keyed), then answer with
      `build` applied to the written game. -/
  | write (w : Write) (keyed : Option Keyed) (build : Game → Res)

/-! ## Routes -/

inductive Op where
  | openGame | listGames | readGame | playMove | resign
  deriving DecidableEq, Repr, Inhabited

def Op.name : Op → String
  | .openGame => "openGame" | .listGames => "listGames" | .readGame => "readGame"
  | .playMove => "playMove" | .resign => "resign"

def routeTable : List (Op × Method × String) := [
  (.openGame, .post, "/games"),
  (.listGames, .get, "/games"),
  (.readGame, .get, "/games/{id:nat}"),
  (.playMove, .post, "/games/{id:nat}/moves"),
  (.resign, .post, "/games/{id:nat}/resignation")]

/-- The compiled table (templates are constants, parsed once). -/
def entries : List (Op × Method × List Seg) :=
  routeTable.filterMap fun (o, m, t) => (parseTemplate t).toOption.map fun s => (o, m, s)

/-! ## Authentication (bearer, opaque tokens by digest) -/

def challenge : String := "Bearer realm=\"games\""

/-- The pure part: the token digest to look up, or the 401 to send. -/
def authDigest (r : Req) : Except Res String :=
  match r.header? "authorization" with
  | none => .error (unauthorized challenge)
  | some v =>
    if ((v.trimAscii.toString.splitOn " ").headD "").toLower != "bearer" then .error (unauthorized challenge)
    else match bearerToken? r with
      | none => .error (unauthorized challenge "invalid credentials")
      | some t => .ok (Tokens.digest t)

def unknownToken : Res := unauthorized challenge "invalid credentials"

/-! ## Inputs -/

inductive Input where
  | openGame (opponent : PlayerId) (tc : TimeControl) (key : Option Keyed)
  | listGames (page per : Nat)
  | readGame (gid : GameId)
  | playMove (gid : GameId) (rev : Revision) (cell : Cell) (key : Option Keyed)
  | resign (gid : GameId) (key : Option Keyed)

instance : FromParam GameId := ⟨fun s => match s.toNat? with
  | some n => GameId.make n
  | none => .error "expected a game id"⟩

instance : SmartCtor PlayerId Nat := ⟨PlayerId.make, (·.n)⟩
instance : SmartCtor Cell Nat := ⟨Cell.make, (·.i)⟩
instance : SmartCtor TimeControl Nat := ⟨TimeControl.make, (·.minutes)⟩

def validKey (k : String) : Bool := Retry.validKey k

/-- The endpoint identity, as the framework renders it (`"<METHOD> <template>"`). -/
def Op.endpoint (op : Op) : String :=
  match routeTable.find? (·.1 == op) with
  | some (_, m, t) => s!"{m} {t}"
  | none => op.name

/-- The key, with the framework's retry identity for this request. -/
def idemKey (op : Op) : Extract (Option Keyed) := fun r =>
  match r.header? "idempotency-key" with
  | none => .ok none
  | some k =>
    if validKey k then .ok (some (Keyed.ofRetry (Retry.ofReq op.endpoint [] k r)))
    else .error [⟨"header.idempotency-key", "1–255 visible ASCII characters"⟩]

/-- `If-Match: "<rev>"`: required on moves (428 when missing). -/
def ifMatchRev (r : Req) : Except Res Revision :=
  match r.header? "if-match" with
  | none => .error (Problem.make 428 (some "If-Match with the resource's ETag is required")).toRes
  | some v =>
    let v := v.trimAscii.toString
    let inner := if v.startsWith "\"" && v.endsWith "\"" && v.length ≥ 2 then ((v.drop 1).dropEnd 1).toString else v
    match inner.toNat? with
    | some n => .ok n
    | none => .error (FieldError.problem [⟨"header.if-match", "expected an ETag \"<revision>\""⟩]).toRes

def jsonOnly (r : Req) : Except Res Unit :=
  if r.contentType? == some "application/json" then .ok ()
  else .error ((Problem.make 415 (some "expected application/json")).withHeader "accept-post" "application/json").toRes

/-- Decoding errors carry field locations; unparseable bodies are 400. -/
def runExtract (x : Extract α) (r : Req) : Except Res α :=
  match x r with
  | .ok a => .ok a
  | .error es =>
    let status := if es.any (fun e => e.loc == "body" && (e.msg.startsWith "invalid JSON" || e.msg == "body is not UTF-8")) then 400 else 422
    .error (FieldError.problem es status).toRes

def decode (op : Op) (r : Req) : Except Res Input :=
  match op with
  | .openGame => do
    jsonOnly r
    runExtract (fun r => do
      let j ← Extract.rawJson r
      let (opp, tc) ← both (field (α := PlayerId) "body" j "opponent") (fieldD "body" j "minutes" TimeControl.default)
      let k ← idemKey .openGame r
      return Input.openGame opp tc k) r
  | .listGames => runExtract (fun r => do
      let (page, per) ← both (Extract.queryD (α := Nat) "page" 1 r) (Extract.queryD (α := Nat) "per" 20 r)
      if page == 0 then .error [⟨"query.page", "must be at least 1"⟩]
      else if per == 0 || per > 100 then .error [⟨"query.per", "must be between 1 and 100"⟩]
      else return Input.listGames page per) r
  | .readGame => runExtract (fun r => Input.readGame <$> Extract.path "id" r) r
  | .playMove => do
    let rev ← ifMatchRev r
    jsonOnly r
    runExtract (fun r => do
      let (gid, cell) ← both (Extract.path (α := GameId) "id" r) (do field (α := Cell) "body" (← Extract.rawJson r) "cell")
      let k ← idemKey .playMove r
      return Input.playMove gid rev cell k) r
  | .resign => runExtract (fun r => do
      let (gid, k) ← both (Extract.path (α := GameId) "id" r) (idemKey .resign r)
      return Input.resign gid k) r

/-! ## Retry identity -/


/-- The retry identity of a request, computed by the framework when it was
    decoded (`idemKey`). Reads have none. -/
def Input.keyed : Input → Option Keyed
  | .openGame _ _ k => k
  | .playMove _ _ _ k => k
  | .resign _ k => k
  | .listGames .. => none
  | .readGame _ => none

/-- The pre-`v1` retry identity (LAPI-10): the operation's short name and
    the SHA-256 of the string each endpoint used to build by hand. Registered
    as `LegacyFingerprint` only so receipts written before the framework
    computed fingerprints still replay. Nothing new is stored with it. -/
def legacyV0 (r : Req) : Option (String × String) :=
  let hex (s : String) := LeanCrypto.Hex.encode (LeanCrypto.sha256 s.toUTF8)
  match routeTable.find? (fun (_, m, t) => s!"{m} {t}" == Retry.opOf r) with
  | none => none
  | some (op, _, _) =>
    match decode op r with
    | .ok (.openGame opp tc _) => some (op.name, hex s!"openGame|{opp.n}|{tc.minutes}")
    | .ok (.playMove gid rev cell _) => some (op.name, hex s!"playMove|{gid.n}|{rev}|{cell.i}")
    | .ok (.resign gid _) => some (op.name, hex s!"resign|{gid.n}")
    | _ => none

/-! ## Loads -/

structure Need where
  game : Option GameId := none
  page : Option (Nat × Nat) := none
  receipt : Option (String × String) := none
  player : Option PlayerId := none

structure Slice where
  game : Option Game := none
  page : List Game × Nat := ([], 0)
  receipt : Option Receipt := none
  playerExists : Bool := false

def Input.need (i : Input) : Need :=
  let base : Need := match i with
    | .openGame opp _ _ => { player := some opp }
    | .listGames page per => { page := some ((page - 1) * per, per) }
    | .readGame gid => { game := some gid }
    | .playMove gid _ _ _ => { game := some gid }
    | .resign gid _ => { game := some gid }
  { base with receipt := i.keyed.map fun k => (k.op, k.key) }

/-! ## Responses (the public projection) -/

def outcomeJson (g : Game) : Json :=
  match g.outcome with
  | .ongoing => Json.mkObj [("state", .str "ongoing"), ("toMove", Json.num g.toMove.n)]
  | .won w => Json.mkObj [("state", .str "won"), ("winner", Json.num w.n)]
  | .drawn => Json.mkObj [("state", .str "drawn")]
  | .resigned l w => Json.mkObj [("state", .str "resigned"), ("loser", Json.num l.n), ("winner", Json.num w.n)]

def gameJson (g : Game) : Json :=
  Json.mkObj [("id", Json.num g.id.n), ("x", Json.num g.x.n), ("o", Json.num g.o.n),
    ("minutes", Json.num g.timeControl.minutes),
    ("moves", Json.arr (g.moves.map fun c => Json.num c.i).toArray),
    ("outcome", outcomeJson g), ("rev", Json.num g.rev)]

def etag (g : Game) : String := s!"\"{g.rev}\""

def gameRes (g : Game) (status : Nat := 200) : Res :=
  (Res.json (gameJson g) status).setHeader "etag" (etag g)

/-- Exists-but-not-visible and does-not-exist give this same response. -/
def hidden : Res := Problem.notFound.toRes

def domainRes : DomainError → Res
  | .staleRevision cur => ((Problem.make 412 (some "the game has changed")).withExt "rev" (Json.num cur)).toRes
  | .notParticipant => hidden
  | .gameOver => (Problem.conflict "the game is over").withExt "code" (.str "game_over") |>.toRes
  | .notYourTurn => (Problem.conflict "not your turn").withExt "code" (.str "not_your_turn") |>.toRes
  | .cellTaken => (Problem.conflict "cell already taken").withExt "code" (.str "cell_taken") |>.toRes
  | .selfPlay => (FieldError.problem [⟨"body.opponent", "cannot play yourself"⟩]).toRes

def keyReused : Res :=
  (Problem.make 422 (some "Idempotency-Key was already used with a different request")).toRes

/-! ## The decision -/

/-- What an operation decides, before retry handling. -/
inductive Decision where
  | respond (res : Res)
  | write (w : Write) (build : Game → Res)

def decideCore (p : PlayerId) (i : Input) (s : Slice) : Decision :=
  match i with
  | .readGame _ =>
    match s.game with
    | none => .respond hidden
    | some g => .respond (gameRes g)
  | .listGames page per =>
    let (items, total) := s.page
    .respond (Res.json (Json.mkObj [("items", Json.arr (items.map gameJson).toArray),
      ("total", Json.num total), ("page", Json.num page), ("per", Json.num per)]))
  | .openGame opp tc _ =>
    if !s.playerExists then .respond (FieldError.problem [⟨"body.opponent", "unknown player"⟩]).toRes else
    match openGame ⟨0⟩ p opp tc with
    | .error e => .respond (domainRes e)
    | .ok g => .write (.insertGame g) fun g => (gameRes g 201).setHeader "location" s!"/games/{g.id.n}"
  | .playMove _ rev cell _ =>
    match s.game with
    | none => .respond hidden
    | some g =>
      match PrivateGames.playMove p rev cell g with
      | .error e => .respond (domainRes e)
      | .ok g' => .write (.updateGame g g') gameRes
  | .resign _ _ =>
    match s.game with
    | none => .respond hidden
    | some g =>
      match PrivateGames.resign p g with
      | .error e => .respond (domainRes e)
      | .ok g' => if g' == g then .respond (gameRes g) else .write (.updateGame g g') gameRes

/-- Replay a recorded outcome, or refuse a reused key, before deciding. -/
def withReceipt (k : Option Keyed) (s : Slice) (decideIt : Unit → Plan) : Plan :=
  match k, s.receipt with
  | some k, some rc => if rc.fingerprint == k.fingerprint then .respond rc.toRes else .respond keyReused
  | _, _ => decideIt ()

/-- The whole pure core: retry handling, then the decision. Every write is
    keyed by the request's own retry identity. -/
def core (p : PlayerId) (i : Input) (s : Slice) : Plan :=
  withReceipt i.keyed s fun _ =>
    match decideCore p i s with
    | .respond r => .respond r
    | .write w build => .write w i.keyed build

end PrivateGames.App
