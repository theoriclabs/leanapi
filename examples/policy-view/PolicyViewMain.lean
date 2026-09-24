import PolicyView.Games
open LeanDb PolicyView PolicyView.Games PrivateGames PrivateGames.Storage

def insertRow (conn : Conn) (α : Type) [Entity α] [HasUnique α] [HasForeignKey α] (v : α) : IO Unit := do
  let c ← match Checked.check v with
    | .ok c => pure c
    | .error _ => throw (IO.userError "row fails its invariant")
  let r ← DbM.run conn (Txn.run (s := Games) (ε := Empty) fun {σ} => do
    let r ← (Txn.insert α c : Txn σ Games Empty _)
    pure (r.toOption.map (·.id.toInt64)))
  match r with
  | .ok (.ok (.ok (some _))) => pure ()
  | _ => throw (IO.userError "insert failed")

def fmt (g : Game) : String := s!"game {g.id.n} ({g.x.n} vs {g.o.n})"

def main : IO Unit := do
  let path : System.FilePath := "policy-view-demo.db"
  if ← path.pathExists then IO.FS.removeFile path
  let conn ← match ← openDb path schema with
    | .ok c => pure c
    | .error e => throw (IO.userError s!"open: {e}")
  -- players 1, 2, 3; game 1 is 1 vs 2, game 2 is 2 vs 3
  for n in ["ann", "bob", "cat"] do insertRow conn PlayerRow { name := n, passwordHash := "-" }
  insertRow conn GameRow (GameRow.ofGame (Game.opened ⟨0⟩ (.lit 1) (.lit 2) TimeControl.default))
  insertRow conn GameRow (GameRow.ofGame (Game.opened ⟨0⟩ (.lit 2) (.lit 3) TimeControl.default))

  let (sql, params) := ReadAs.getSql (s := Games) GameRow (PlayerId.lit 1) (gidRef ⟨2⟩)
  IO.println s!"SQL filter for player 1 asking for game 2:\n  WHERE {sql}\n  params {params.toList.map (·.describe)}\n"

  for (p, gid) in [(1, 1), (1, 2), (3, 2), (3, 1)] do
    match ← runAs conn (PlayerId.ofNat! p) (fun me => readGame me ⟨gid⟩) with
    | .ok (.ok g) => IO.println s!"player {p} reads game {gid}: {(g.map fmt).getD "none (404)"}"
    | _ => IO.println "fault"
  for p in [1, 2, 3] do
    match ← runAs conn (PlayerId.ofNat! p) myGames with
    | .ok (.ok gs) => IO.println s!"player {p} lists: {gs.map fmt}"
    | _ => IO.println "fault"
