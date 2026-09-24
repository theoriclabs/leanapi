import Scheduling.Api

open Scheduling LeanDb LeanApi

def usage : String := "usage: scheduling [--host 127.0.0.1] [--port 8080] [--db calendar.sqlite]"

partial def parse (args : List String) (host : String) (port : Nat) (db : String) :
    Except String (String × Nat × String) :=
  match args with
  | [] => .ok (host, port, db)
  | "--host" :: h :: rest => parse rest h port db
  | "--port" :: p :: rest => match p.toNat? with
    | some n => parse rest host n db
    | none => .error usage
  | "--db" :: d :: rest => parse rest host port d
  | _ => .error usage

def mustHandle (s : String) : IO Handle :=
  match Handle.make s with
  | .ok h => pure h
  | .error e => throw (IO.userError e)

def insertPerson (conn : Conn) (handle token : String) : IO Unit := do
  let h ← mustHandle handle
  let row := PersonRow.checked { handle := h, digest := Tokens.digest token }
  let r ← DbM.run conn (Txn.run (s := Calendar) (ε := Unit) fun {_σ} => do
    match ← Txn.insert PersonRow row with
    | .ok _ => pure ()
    | .error _ => Txn.throw ())
  match r with
  | .ok (.ok (.ok ())) => pure ()
  | _ => throw (IO.userError s!"seed person {handle} failed")

def seedIfEmpty (conn : Conn) : IO Unit := do
  let counted ← DbM.run conn (Read.run (s := Calendar) (Read.count (LeanDb.Query.from PersonRow)))
  match counted with
  | .ok (.ok 0) =>
    insertPerson conn "alice" "alice-token"
    insertPerson conn "bob" "bob-token"
    IO.eprintln "seeded alice (id 1, token alice-token) and bob (id 2, token bob-token)"
    let (sql, params) := busySql (PersonId.lit 1)
    IO.eprintln s!"busy SQL for host 1:\n  WHERE {sql}\n  params {params.toList.map (·.describe)}"
  | .ok (.ok _) =>
    IO.eprintln "database already has people; tokens are whatever you seeded"
  | _ => throw (IO.userError "could not count people")

def main (args : List String) : IO UInt32 := do
  let env ← IO.getEnv "PORT"
  match parse args "127.0.0.1" ((env.bind String.toNat?).getD 8080) "calendar.sqlite" with
  | .error u => IO.eprintln u; return 3
  | .ok (host, port, db) =>
    let dc ← DbConns.open db schema
    -- Seed on the writer connection before serving.
    seedIfEmpty dc.writer.conn
    let svc := service dc
    IO.eprintln (stack).describe
    IO.eprintln calendarApi.describe
    LeanApi.serve svc { host, port := port.toUInt16 }
    dc.close
    return 0
