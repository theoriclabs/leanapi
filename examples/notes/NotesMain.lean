import Notes.App

def main (args : List String) : IO Unit := do
  let port := (args.getD 0 "8080").toNat?.getD 8080
  let db ← Notes.Db.new
  let svc := Notes.service db
  IO.eprintln (Notes.stack.describe)
  LeanApi.serve svc { port := port.toUInt16 }
