/-
  Usage-based billing over SQLite: each event counted once, invoice
  totals match their lines, finalized invoices stay put, tenants isolated.
-/
import Billing.Api

namespace Tests.Billing

open LeanApi LeanApi.Test Lean LeanDb
open _root_.Billing _root_.Billing.Schema _root_.Billing.Api

private def freshPath (name : String) : IO System.FilePath := do
  let dir : System.FilePath := ".lake/test-db"
  IO.FS.createDirAll dir
  let path := dir / s!"{name}.sqlite"
  for ext in ["", "-wal", "-shm"] do
    let f : System.FilePath := path.toString ++ ext
    if ← f.pathExists then IO.FS.removeFile f
  return path

private def bearer (t : String) : String × String := ("Authorization", s!"Bearer {t}")

private def tenantRow (key : String) (cents : Nat) (hc : cents ≤ maxUnitPrice) : IO TenantRow :=
  match ApiKey.make key with
  | .ok k => pure ⟨k, ⟨cents, hc⟩⟩
  | .error e => throw (IO.userError e)

private def seedTenant {σ} (row : TenantRow) : Txn σ BillingDb Unit Unit := do
  match ← Txn.insert (α := TenantRow) (TenantRow.checked row) with
  | .ok _ => pure ()
  | .error _ => pure ()

private def seed (conn : Conn) : IO Unit := do
  let acme ← tenantRow "acme-live-key" 10 (by decide)
  let beta ← tenantRow "beta-live-key" 25 (by decide)
  let r ← DbM.run conn (Txn.run (s := BillingDb) (ε := Unit) fun {σ} => do
    seedTenant (σ := σ) acme
    seedTenant (σ := σ) beta)
  match r with
  | .ok (.ok (.ok _)) => pure ()
  | _ => throw (IO.userError "seed failed")

private def jnat (r : Reply) (k : String) : Option Nat :=
  r.json?.bind fun j => (j.getObjValAs? Nat k).toOption

private def jstr (r : Reply) (k : String) : Option String :=
  r.json?.bind fun j => (j.getObjValAs? String k).toOption

private def usageBody (eventId : String) (qty : Nat) : Json :=
  Json.mkObj [("eventId", .str eventId), ("quantity", Json.num qty),
    ("occurredAt", Json.num 1727136000),
    ("period", Json.mkObj [("year", Json.num 2026), ("month", Json.num 9)])]

private def invoiceBody : Json :=
  Json.mkObj [("period", Json.mkObj [("year", Json.num 2026), ("month", Json.num 9)])]

def run : TestM Unit := do
  section_ "billing: ingest once, isolate tenants, freeze finalized invoices" do
    let path ← freshPath "billing"
    let dc ← LeanApi.DbConns.open path schema 2
    seed dc.writer.conn
    let svc := service dc (log := fun _ => pure ())
    let acme := [bearer "acme-live-key"]
    let beta := [bearer "beta-live-key"]

    let r1 ← postJson svc "/usage" (usageBody "evt_1" 3) acme
    checkEq "ingest 201" r1.status 201
    checkEq "ingest location" (r1.header? "location") (some "/usage/evt_1")
    checkEq "ingest quantity" (jnat r1 "quantity") (some 3)
    checkEq "first is not a replay" (r1.header? "idempotent-replayed") none

    let r2 ← postJson svc "/usage" (usageBody "evt_1" 3) acme
    checkEq "resend 201" r2.status 201
    checkEq "resend marked replay" (r2.header? "idempotent-replayed") (some "true")
    checkEq "resend same body" r2.body r1.body
    checkEq "resend same location" (r2.header? "location") (r1.header? "location")

    let r3 ← postJson svc "/usage" (usageBody "evt_1" 9) acme
    checkEq "same id, other quantity: 409" r3.status 409
    checkEq "same id, other quantity: not a replay" (r3.header? "idempotent-replayed") none
    checkEq "conflict detail"
      (jstr r3 "detail") (some "event id already used for a different event")
    checkEq "conflict body has no quantity" (jnat r3 "quantity") none
    checkEq "stored event unchanged after conflict"
      (jnat (← get svc "/usage/evt_1" acme) "quantity") (some 3)

    checkEq "beta cannot read acme's event" (← get svc "/usage/evt_1" beta).status 404
    checkEq "acme can read own event" (← get svc "/usage/evt_1" acme).status 200
    checkEq "missing event 404" (← get svc "/usage/nope" acme).status 404
    checkEq "no auth 401" (← get svc "/usage/evt_1").status 401
    checkEq "bad key 401" (← get svc "/usage/evt_1" [bearer "nope-nope"]).status 401

    let other ← get svc "/usage/evt_1" beta
    let missing ← get svc "/usage/missing-event" beta
    checkEq "other's event ≡ missing (status)" other.status missing.status
    checkEq "other's event ≡ missing (body)" other.body missing.body

    let inv1 ← postJson svc "/invoices" invoiceBody acme
    checkEq "invoice 201" inv1.status 201
    checkEq "invoice status draft" (jstr inv1 "status") (some "draft")
    checkEq "3 × 10¢ = 30" (inv1.json?.bind fun j =>
      (j.getObjVal? "total").toOption.bind fun t => (t.getObjValAs? Nat "amount").toOption) (some 30)
    let iid := (jnat inv1 "id").getD 0

    let inv2 ← postJson svc "/invoices" invoiceBody acme
    checkEq "same period replays" (inv2.header? "idempotent-replayed") (some "true")
    checkEq "same period same body" inv2.body inv1.body

    checkEq "beta cannot read acme's invoice" (← get svc s!"/invoices/{iid}" beta).status 404
    checkEq "acme reads own invoice" (← get svc s!"/invoices/{iid}" acme).status 200
    let otherI ← get svc s!"/invoices/{iid}" beta
    let missingI ← get svc "/invoices/99999" beta
    checkEq "other's invoice ≡ missing (status)" otherI.status missingI.status
    checkEq "other's invoice ≡ missing (body)" otherI.body missingI.body

    checkEq "pay while draft 409" (← request svc "POST" s!"/invoices/{iid}/pay" acme).status 409
    checkEq "finalize 200" (← request svc "POST" s!"/invoices/{iid}/finalize" acme).status 200
    let fin ← get svc s!"/invoices/{iid}" acme
    checkEq "now finalized" (jstr fin "status") (some "finalized")
    checkEq "lines unchanged at finalize" (fin.json?.bind fun j =>
      (j.getObjVal? "total").toOption.bind fun t => (t.getObjValAs? Nat "amount").toOption) (some 30)

    checkEq "finalize again 409" (← request svc "POST" s!"/invoices/{iid}/finalize" acme).status 409
    checkEq "pay 200" (← request svc "POST" s!"/invoices/{iid}/pay" acme).status 200
    let paid ← get svc s!"/invoices/{iid}" acme
    checkEq "now paid" (jstr paid "status") (some "paid")
    checkEq "lines unchanged at pay" (paid.json?.bind fun j =>
      (j.getObjVal? "total").toOption.bind fun t => (t.getObjValAs? Nat "amount").toOption) (some 30)
    checkEq "void after pay 409" (← request svc "POST" s!"/invoices/{iid}/void" acme).status 409

    let _ ← postJson svc "/usage" (usageBody "evt_b" 2) beta
    let binv ← postJson svc "/invoices" invoiceBody beta
    checkEq "beta's invoice 201" binv.status 201
    checkEq "2 × 25¢ = 50" (binv.json?.bind fun j =>
      (j.getObjVal? "total").toOption.bind fun t => (t.getObjValAs? Nat "amount").toOption) (some 50)
    let bid := (jnat binv "id").getD 0
    checkEq "void 200" (← request svc "POST" s!"/invoices/{bid}/finalize" beta).status 200
    checkEq "void finalized" (← request svc "POST" s!"/invoices/{bid}/void" beta).status 200
    checkEq "now void" (jstr (← get svc s!"/invoices/{bid}" beta) "status") (some "void")

    check "describe prints the Tx signature"
      ((billingApi.describe.splitOn "Tx BillingDb BillingError (Replayed (Created UsageView))").length > 1)

    -- Concurrent ingest of the same event: one insert, the rest replays.
    let tasks ← (List.range 6).mapM fun _ => IO.asTask (postJson svc "/usage" (usageBody "evt_race" 1) acme)
    let mut n := 0
    let mut replay := 0
    for t in tasks do
      match ← IO.wait t with
      | .ok r =>
        if r.status == 201 then n := n + 1
        if r.header? "idempotent-replayed" == some "true" then replay := replay + 1
      | .error _ => pure ()
    checkEq "concurrent ingest all 201" n 6
    check "concurrent ingest: at least one replay" (replay != 0)
    checkEq "GET after race is the original quantity"
      (jnat (← get svc "/usage/evt_race" acme) "quantity") (some 1)

    dc.close

end Tests.Billing
