import PrivateGames.App.Service

open PrivateGames.App PrivateGames.Storage

def usage : String := "usage: games [--host 127.0.0.1] [--port 8080] [--db games.sqlite]"

partial def parse (args : List String) (host : String) (port : Nat) (db : String) : Except String (String × Nat × String) :=
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
  match parse args "127.0.0.1" ((env.bind String.toNat?).getD 8080) "games.sqlite" with
  | .error u => IO.eprintln u; return 3
  | .ok (host, port, db) =>
    let rt ← Runtime.open db
    let dummy ← LeanCrypto.Password.hash "leanapi-dummy-password"
    let draining ← IO.mkRef false
    let svc := LeanApi.Service.ofRouter (LeanApi.Router.build! (routes rt.repo dummy))
      (stack IO.eprintln (do return !(← draining.get)))
    IO.eprintln (stack).describe
    LeanApi.serve svc { host, port := port.toUInt16 } (draining := some draining)
    rt.close
    return 0
