import TeamsDemo.Api

open TeamsDemo LeanApi

def usage : String := "usage: teamsdemo [--host 127.0.0.1] [--port 8080] [--db teams.sqlite]"

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

def main (args : List String) : IO UInt32 := do
  match parse args "127.0.0.1" 8080 "teams.sqlite" with
  | .error u => IO.eprintln u; return 3
  | .ok (host, port, db) =>
    let path : System.FilePath := db
    let fresh := !(← path.pathExists)
    let dc ← DbConns.open path TeamsDemo.schema
    if fresh then seed dc.writer.conn
    IO.eprintln teamsApi.describe
    serve (teamsApi.service dc) { host, port := port.toUInt16 }
    dc.close
    return 0
