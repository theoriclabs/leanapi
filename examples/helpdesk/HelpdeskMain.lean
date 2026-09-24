import Helpdesk.Api

open Helpdesk LeanApi

def usage : String := "usage: helpdesk [--host 127.0.0.1] [--port 8080] [--db helpdesk.sqlite]"

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
  let env ← IO.getEnv "PORT"
  match parse args "127.0.0.1" ((env.bind String.toNat?).getD 8080) "helpdesk.sqlite" with
  | .error u => IO.eprintln u; return 3
  | .ok (host, port, db) =>
    let path : System.FilePath := db
    let already ← path.pathExists
    let dc ← DbConns.open path Helpdesk.schema
    unless already do seed dc.writer.conn
    let svc := helpdeskApi.service dc (stack := stack IO.eprintln)
    IO.eprintln (stack).describe
    IO.eprintln helpdeskApi.describe
    serve svc { host, port := port.toUInt16 }
    dc.close
    return 0
