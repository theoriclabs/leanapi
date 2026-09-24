import Billing.Api

open LeanApi LeanDb Billing Billing.Schema Billing.Api

def usage : String := "usage: billing [--host 127.0.0.1] [--port 8080] [--db billing.sqlite]"

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

def tenantRow (key : String) (cents : Nat) (hc : cents ≤ maxUnitPrice) : IO TenantRow :=
  match ApiKey.make key with
  | .ok k => pure ⟨k, ⟨cents, hc⟩⟩
  | .error e => throw (IO.userError e)

def seedTenant {σ} (row : TenantRow) : Txn σ BillingDb Unit Unit := do
  match ← Txn.insert (α := TenantRow) (TenantRow.checked row) with
  | .ok _ => pure ()
  | .error _ => pure ()

def seed (conn : Conn) : IO Unit := do
  let acme ← tenantRow "acme-live-key" 10 (by decide)
  let beta ← tenantRow "beta-live-key" 25 (by decide)
  let r ← DbM.run conn (Txn.run (s := BillingDb) (ε := Unit) fun {σ} => do
    seedTenant (σ := σ) acme
    seedTenant (σ := σ) beta)
  match r with
  | .ok (.ok (.ok _)) => pure ()
  | _ => throw (IO.userError "seed failed")

def main (args : List String) : IO UInt32 := do
  let env ← IO.getEnv "PORT"
  match parse args "127.0.0.1" ((env.bind String.toNat?).getD 8080) "billing.sqlite" with
  | .error u => IO.eprintln u; return 3
  | .ok (host, port, db) =>
    let dc ← LeanApi.DbConns.open db schema
    seed dc.writer.conn
    let draining ← IO.mkRef false
    let svc := service dc
    IO.eprintln (stack).describe
    IO.eprintln billingApi.describe
    IO.eprintln "tenants: acme-live-key (10¢/unit), beta-live-key (25¢/unit)"
    LeanApi.serve svc { host, port := port.toUInt16 } (draining := some draining)
    dc.close
    return 0
