import PrivateGames.App.Service

namespace Tests.Games

open LeanApi LeanApi.Test Lean PrivateGames PrivateGames.App PrivateGames.Storage

def fast : LeanCrypto.Password.Params := { logN := 8 }

def jnat (r : Reply) (k : String) : Option Nat := r.json?.bind fun j => (j.getObjValAs? Nat k).toOption
def jstr (r : Reply) (k : String) : Option String := r.json?.bind fun j => (j.getObjValAs? String k).toOption

structure Env where
  path : System.FilePath
  rt : Runtime
  svc : Service

def freshEnv (name : String) : IO Env := do
  let dir : System.FilePath := ".lake/test-db"
  IO.FS.createDirAll dir
  let path := dir / s!"{name}.sqlite"
  for ext in ["", "-wal", "-shm"] do
    let f : System.FilePath := path.toString ++ ext
    if ← f.pathExists then IO.FS.removeFile f
  let rt ← Runtime.open path 2
  let dummy ← LeanCrypto.Password.hash "dummy" fast
  return { path, rt, svc := service rt.repo dummy (fun _ => pure ()) fast }

def signup (svc : Service) (name : String) : IO (Nat × String) := do
  let r ← postJson svc "/players" (Json.mkObj [("name", .str name), ("password", .str s!"pw-{name}-long")])
  let id := (jnat r "id").getD 0
  let s ← request svc "POST" "/sessions" [("Authorization", "Basic " ++ Base64.encode s!"{name}:pw-{name}-long".toUTF8)]
  return (id, (jstr s "token").getD "")

def bearer (t : String) : String × String := ("Authorization", s!"Bearer {t}")

def openGame (svc : Service) (tok : String) (opp : Nat) (extra : List (String × String) := []) : IO Reply :=
  postJson svc "/games" (Json.mkObj [("opponent", Json.num opp)]) (bearer tok :: extra)

def move (svc : Service) (tok : String) (gid rev cell : Nat) (extra : List (String × String) := []) : IO Reply :=
  request svc "POST" s!"/games/{gid}/moves"
    ([bearer tok, ("Content-Type", "application/json"), ("If-Match", s!"\"{rev}\"")] ++ extra)
    (Json.mkObj [("cell", Json.num cell)]).compress

def run : TestM Unit := do
  let env ← freshEnv "games"
  let svc := env.svc
  let (aliceId, alice) ← signup svc "alice"
  let (bobId, bob) ← signup svc "bob"
  let (_, eve) ← signup svc "eve"

  section_ "accounts (unproved routes)" do
    check "tokens issued" (!alice.isEmpty && !bob.isEmpty && !eve.isEmpty)
    checkEq "duplicate name 409" (← postJson svc "/players" (Json.mkObj [("name", .str "alice"), ("password", .str "whatever-long")])).status 409
    checkEq "wrong password 401" (← request svc "POST" "/sessions" [("Authorization", "Basic " ++ Base64.encode "alice:nope".toUTF8)]).status 401

  section_ "open, read, list" do
    let r ← openGame svc alice bobId
    checkEq "open 201" r.status 201
    let gid := (jnat r "id").getD 0
    checkEq "location" (r.header? "location") (some s!"/games/{gid}")
    checkEq "etag rev 0" (r.header? "etag") (some "\"0\"")
    checkEq "self-play 422" (← openGame svc alice aliceId).status 422
    checkEq "unknown opponent 422" (← openGame svc alice 9999).status 422
    checkEq "wrapped opponent id refused" (← openGame svc alice (2^64 + bobId)).status 422
    checkEq "bad opponent 422" (← postJson svc "/games" (Json.mkObj [("opponent", .str "x")]) [bearer alice]).status 422
    checkEq "x reads" (← get svc s!"/games/{gid}" [bearer alice]).status 200
    checkEq "o reads" (← get svc s!"/games/{gid}" [bearer bob]).status 200
    let r ← get svc "/games" [bearer bob]
    checkEq "bob lists 1" (jnat r "total") (some 1)
    let r ← get svc "/games" [bearer eve]
    checkEq "eve lists 0" (jnat r "total") (some 0)
    checkEq "no auth 401" (← get svc s!"/games/{gid}").status 401
    checkEq "wrapped game id refused" (← get svc s!"/games/{2^64 + gid}" [bearer alice]).status 422
    checkEq "unknown token 401" (← get svc s!"/games/{gid}" [bearer "nope"]).status 401
    checkEq "per too big 422" (← get svc "/games?per=500" [bearer bob]).status 422

  section_ "list count and page share a WAL snapshot" do
    let snapshotEnv ← freshEnv "list-snapshot"
    let (ownerId, owner) ← signup snapshotEnv.svc "snapshot-owner"
    let (peerId, _) ← signup snapshotEnv.svc "snapshot-peer"
    let _ ← openGame snapshotEnv.svc owner peerId
    if let some reader := snapshotEnv.rt.readConns[0]? then
      let observed ← LeanDb.DbM.run reader (readSnapshot do
        let before ← LeanDb.countP (visiblePred ⟨ownerId⟩)
        -- A different connection commits after the count and before the page.
        let inserted ← liftM <| LeanDb.DbM.run snapshotEnv.rt.writeConn
          (LeanDb.insert GameRow (GameRow.ofGame
            (Game.opened ⟨0⟩ ⟨ownerId⟩ ⟨peerId⟩ TimeControl.default)))
        let after ← LeanDb.countP (visiblePred ⟨ownerId⟩)
        let page ← LeanDb.fetchFiltered GameRow (visiblePred ⟨ownerId⟩)
          (window := { limit := some 10, offset := 0 })
        return (before, after, page.size, inserted.isOk))
      checkEq "count and page see the same version" observed.toOption (some (1, 1, 1, true))
      let listed ← snapshotEnv.rt.repo.listVisible ⟨ownerId⟩ 0 10
      checkEq "new game visible after snapshot ends" (listed.toOption.map Prod.snd) (some 2)
    else
      check "snapshot reader exists" false
    snapshotEnv.rt.close

  section_ "§9.3: unauthorized vs missing ids" do
    let gid := 1
    let other ← get svc s!"/games/{gid}" [bearer eve]
    let missing ← get svc "/games/424242" [bearer eve]
    checkEq "status equal" other.status missing.status
    checkEq "body equal" other.body missing.body
    checkEq "is 404" other.status 404
    let mo ← move svc eve gid 0 4
    let mm ← move svc eve 424242 0 4
    checkEq "move on other's game ≡ missing (status)" mo.status mm.status
    checkEq "move on other's game ≡ missing (body)" mo.body mm.body
    let ro ← request svc "POST" s!"/games/{gid}/resignation" [bearer eve]
    let rm ← request svc "POST" "/games/424242/resignation" [bearer eve]
    checkEq "resign on other's game ≡ missing" (ro.status, ro.body) (rm.status, rm.body)
    let g ← get svc s!"/games/{gid}" [bearer alice]
    checkEq "eve's attempts changed nothing" (g.header? "etag") (some "\"0\"")

  section_ "moves, If-Match, stale revision" do
    let gid := 1
    checkEq "missing If-Match 428" (← request svc "POST" s!"/games/{gid}/moves" [bearer alice, ("Content-Type", "application/json")] "{\"cell\":4}").status 428
    checkEq "bad cell 422" (← move svc alice gid 0 9).status 422
    let r ← move svc alice gid 0 4
    checkEq "x plays center" r.status 200
    checkEq "rev 1" (r.header? "etag") (some "\"1\"")
    checkEq "stale rev 412" (← move svc bob gid 0 0).status 412
    checkEq "not your turn 409" (← move svc alice gid 1 0).status 409
    checkEq "cell taken 409" (← move svc bob gid 1 4).status 409
    checkEq "o plays" (← move svc bob gid 1 0).status 200

  section_ "keyed idempotence" do
    let (_, carol) ← signup svc "carol"
    let (daveId, dave) ← signup svc "dave"
    let r1 ← openGame svc carol daveId [("Idempotency-Key", "open-1")]
    let r2 ← openGame svc carol daveId [("Idempotency-Key", "open-1")]
    checkEq "replayed open: same status" r2.status r1.status
    checkEq "replayed open: same body" r2.body r1.body
    checkEq "replay marked" (r2.header? "idempotent-replayed") (some "true")
    let r ← get svc "/games" [bearer carol]
    checkEq "only one game opened" (jnat r "total") (some 1)
    checkEq "same key + same input, other headers: replay" (← openGame svc carol daveId [("Idempotency-Key", "open-1"), ("X", "y")]).status 201
    let diff ← postJson svc "/games" (Json.mkObj [("opponent", Json.num daveId), ("minutes", Json.num 5)]) [bearer carol, ("Idempotency-Key", "open-1")]
    checkEq "same key + different input 422" diff.status 422
    let gid := (jnat r1 "id").getD 0
    let m1 ← move svc carol gid 0 4 [("Idempotency-Key", "m-1")]
    checkEq "keyed move ok" m1.status 200
    let m2 ← move svc carol gid 0 4 [("Idempotency-Key", "m-1")]
    checkEq "keyed replay same body" m2.body m1.body
    checkEq "keyed replay same status (not 412)" m2.status 200
    checkEq "keyed replay did not advance" ((← get svc s!"/games/{gid}" [bearer carol]).header? "etag") (some "\"1\"")
    let m3 ← move svc carol gid 0 5 [("Idempotency-Key", "m-1")]
    checkEq "§9.3 key reuse with different body 422" m3.status 422
    let m4 ← move svc dave gid 1 0 [("Idempotency-Key", "m-1")]
    checkEq "keys are per actor" m4.status 200
    let r ← request svc "POST" s!"/games/{gid}/resignation" [bearer dave, ("Idempotency-Key", "res")]
    checkEq "resign" r.status 200
    let r' ← request svc "POST" s!"/games/{gid}/resignation" [bearer dave]
    checkEq "unkeyed resign again: state idempotent 200" r'.status 200
    checkEq "resign again: same body" r'.body r.body

  section_ "§9.3: simultaneous moves" do
    let (_, p1) ← signup svc "p1"
    let (p2Id, _) ← signup svc "p2"
    let gid := (jnat (← openGame svc p1 p2Id) "id").getD 0
    let tasks ← (List.range 8).mapM fun i => IO.asTask (move svc p1 gid 0 i)
    let mut ok := 0
    let mut stale := 0
    for t in tasks do
      match ← IO.wait t with
      | .ok r => if r.status == 200 then ok := ok + 1 else if r.status == 412 then stale := stale + 1
      | .error _ => pure ()
    checkEq "exactly one concurrent move wins" ok 1
    checkEq "the rest are 412" stale 7
    let g ← get svc s!"/games/{gid}" [bearer p1]
    checkEq "one move recorded" (g.json?.bind fun j => (j.getObjVal? "moves").toOption.map fun
      | .arr xs => xs.size | _ => 0) (some 1)
    -- same key, concurrently: one commit, the rest replay or conflict, never two commits
    let (_, q1) ← signup svc "q1"
    let (q2Id, _) ← signup svc "q2"
    let gid := (jnat (← openGame svc q1 q2Id) "id").getD 0
    let tasks ← (List.range 6).mapM fun _ => IO.asTask (move svc q1 gid 0 8 [("Idempotency-Key", "same")])
    let mut statuses := #[]
    for t in tasks do
      if let .ok r ← IO.wait t then statuses := statuses.push r.status
    check "concurrent same key: all 200 (commit or replay) or 412" (statuses.all (fun s => s == 200 || s == 412))
    checkEq "concurrent same key: one transition" ((← get svc s!"/games/{gid}" [bearer q1]).header? "etag") (some "\"1\"")

  section_ "§9.3: revocation between admission and commit" do
    -- bob loses participation between the load and the commit: simulated by
    -- replacing the stored game's participants under the same revision
    let (_, r1) ← signup svc "r1"
    let (r2Id, _) ← signup svc "r2"
    let (r3Id, _) ← signup svc "r3"
    let gid := (jnat (← openGame svc r1 r2Id) "id").getD 0
    let repo := env.rt.repo
    let some g ← (do match ← repo.loadVisible ⟨r2Id⟩ ⟨gid⟩ with | .ok g => pure g | .error _ => pure none)
      | check "loaded" false
    -- admission happened against `g`; now the row changes participants
    let conn := env.rt.writeConn
    let _ ← LeanDb.DbM.run conn do
      match ← LeanDb.get (gidRef ⟨gid⟩) with
      | some s => let _ ← LeanDb.update s { s.val with o := pref ⟨r3Id⟩ }; pure ()
      | none => pure ()
    let res ← repo.commit ⟨r2Id⟩ (.updateGame g { g with resigned := some ⟨r2Id⟩, rev := g.rev + 1 }) none gameRes
    check "commit refused after revocation" (match res with | .error .notFound => true | _ => false)
    let now ← get svc s!"/games/{gid}" [bearer r1]
    checkEq "state unchanged" (now.header? "etag") (some "\"0\"")

  section_ "stored row that fails validation" do
    let (_, s1) ← signup svc "s1"
    let (s2Id, _) ← signup svc "s2"
    let gid := (jnat (← openGame svc s1 s2Id) "id").getD 0
    let _ ← LeanDb.DbM.run env.rt.writeConn do
      match ← LeanDb.get (gidRef ⟨gid⟩) with
      | some s => let _ ← LeanDb.update s { s.val with rev := 7 }; pure ()
      | none => pure ()
    let r ← get svc s!"/games/{gid}" [bearer s1]
    checkEq "invalid stored game → 500, not a crash" r.status 500
    check "no internal detail" (!r.body.contains "Valid")
    let l ← get svc "/games" [bearer s1]
    checkEq "list with invalid row → 500" l.status 500
    checkEq "other users unaffected" (← get svc "/games" [bearer alice]).status 200

  section_ "§9.3: restart after commit, retry returns the receipt" do
    let (_, t1) ← signup svc "t1"
    let (t2Id, _) ← signup svc "t2"
    let gid := (jnat (← openGame svc t1 t2Id) "id").getD 0
    let first ← move svc t1 gid 0 2 [("Idempotency-Key", "before-crash")]
    env.rt.close
    -- the response was "lost"; the process restarts on the same file
    let rt2 ← Runtime.open env.path 1
    let dummy ← LeanCrypto.Password.hash "dummy" fast
    let svc2 := service rt2.repo dummy (fun _ => pure ()) fast
    let retry ← move svc2 t1 gid 0 2 [("Idempotency-Key", "before-crash")]
    checkEq "retry after restart: status" retry.status first.status
    checkEq "retry after restart: body" retry.body first.body
    checkEq "retry marked as replay" (retry.header? "idempotent-replayed") (some "true")
    checkEq "applied once" ((← get svc2 s!"/games/{gid}" [bearer t1]).header? "etag") (some "\"1\"")
    rt2.close

end Tests.Games
