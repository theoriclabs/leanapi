/-
  Help desk: tenant isolation, internal notes, closed tickets, exactly-once
  inbound. Runtime tests over SQLite; compile-time refusals pinned with
  `#guard_msgs`.
-/
import Helpdesk.Api
import LeanApi

namespace Tests.HelpdeskHttp

open LeanApi LeanApi.Test Lean LeanDb PolicyView
open _root_.Helpdesk

def bearer (t : String) : String × String := ("Authorization", s!"Bearer {t}")

def jnat (r : Reply) (k : String) : Option Nat :=
  r.json?.bind fun j => (j.getObjValAs? Nat k).toOption

def jbool (r : Reply) (k : String) : Option Bool :=
  r.json?.bind fun j => (j.getObjValAs? Bool k).toOption

def arrLen (r : Reply) : Nat :=
  match r.json? with
  | some (.arr xs) => xs.size
  | _ => 0

def msgsLen (r : Reply) : Nat :=
  match r.json? with
  | some (.obj m) =>
    match m.get? "messages" with
    | some (.arr xs) => xs.size
    | _ => 0
  | _ => 0

def anyInternal (r : Reply) : Bool :=
  match r.json? with
  | some (.obj m) =>
    match m.get? "messages" with
    | some (.arr xs) => xs.any fun
      | .obj o => match o.get? "internal" with
        | some (.bool true) => true
        | _ => false
      | _ => false
    | _ => false
  | _ => false

def fresh (name : String) : IO (DbConns × Service) := do
  let dir : System.FilePath := ".lake/test-db"
  IO.FS.createDirAll dir
  let path := dir / s!"{name}.sqlite"
  for ext in ["", "-wal", "-shm"] do
    let f : System.FilePath := path.toString ++ ext
    if ← f.pathExists then IO.FS.removeFile f
  let dc ← DbConns.open path Helpdesk.schema 1
  seed dc.writer.conn
  return (dc, helpdeskApi.service dc (log := fun _ => pure ()))

-- A GET whose handler writes does not build.
/-- error: could not synthesize default value for parameter 'safe' using tactics
---
error: a GET or HEAD endpoint must not change state, but this handler's effect is `writes`. Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.
⊢ (Handler.effect (DbState HelpdeskDb)
      (Auth Who → Path TicketId → Body ReplyBody → Now → LeanApi.Tx HelpdeskDb HelpError (Created MessageView))).Safe -/
#guard_msgs (error) in
example : DbEndpoint HelpdeskDb := .get "/tickets/{id:nat}/messages" postMessage

-- `TxAs.mk` is private, so an unscoped `Txn` cannot enter the write view.
-- This check lives outside `Helpdesk.Policies`.
/-- error: Invalid `⟨...⟩` notation: Constructor for `Helpdesk.TxAs` is marked as private -/
#guard_msgs (substring := true) in
def sneakyWrite (me : Who) : TxAs HelpdeskDb me String Unit :=
  ⟨Txn.throw "nope"⟩

def run : TestM Unit := do
  let (dc, svc) ← fresh "helpdesk"
  let ada := [bearer "ada"]
  let carl := [bearer "carl"]
  let gwen := [bearer "gwen"]
  let gina := [bearer "gina"]

  section_ "helpdesk auth" do
    checkEq "no token 401" (← get svc "/tickets").status 401
    checkEq "bad token 401" (← get svc "/tickets" [bearer "nope"]).status 401
    checkEq "ada lists 200" (← get svc "/tickets" ada).status 200

  section_ "helpdesk inbound exactly-once" do
    let body := Json.mkObj [
      ("messageId", .str "<m1@acme>"),
      ("requester", Json.num 2),
      ("subject", .str "Login broken"),
      ("body", .str "I cannot sign in.")]
    let r1 ← postJson svc "/inbound" body ada
    checkEq "inbound 201" r1.status 201
    let tid := (jnat r1 "id").getD 0
    check "ticket id" (tid > 0)
    checkEq "location" (r1.header? "location") (some s!"/tickets/{tid}")
    let r2 ← postJson svc "/inbound" body ada
    checkEq "retry 200" r2.status 200
    checkEq "retry same id" (jnat r2 "id") (some tid)
    let listed ← get svc "/tickets" carl
    checkEq "carl lists 1" (arrLen listed) 1
    checkEq "gina lists 0 before globex inbound" (arrLen (← get svc "/tickets" gina)) 0
    -- Same Message-ID in another org is a different ticket.
    let gbody := Json.mkObj [
      ("messageId", .str "<m1@acme>"),
      ("requester", Json.num 4),
      ("subject", .str "Login broken"),
      ("body", .str "I cannot sign in.")]
    let rg ← postJson svc "/inbound" gbody gwen
    checkEq "globex inbound 201" rg.status 201
    check "different ticket" ((jnat rg "id").getD 0 != tid)

  section_ "helpdesk tenant isolation" do
    let listed ← get svc "/tickets" gina
    checkEq "gina lists her own, not acme" (arrLen listed) 1
    checkEq "gina does not see ticket 1" (← get svc "/tickets/1" gina).status 404
    let other ← get svc "/tickets/1" gwen
    let missing ← get svc "/tickets/424242" gwen
    checkEq "other org status ≡ missing" other.status missing.status
    checkEq "other org body ≡ missing" other.body missing.body
    checkEq "is 404" other.status 404
    let carls ← get svc "/tickets" carl
    checkEq "carl still lists 1" (arrLen carls) 1

  section_ "helpdesk internal notes" do
    let note := Json.mkObj [("body", .str "Reset their password."), ("internal", .bool true)]
    let r ← postJson svc "/tickets/1/messages" note ada
    checkEq "agent internal 201" r.status 201
    checkEq "flag true" (jbool r "internal") (some true)
    let asAda ← get svc "/tickets/1" ada
    checkEq "agent sees thread 200" asAda.status 200
    check "agent sees internal" (anyInternal asAda)
    check "agent sees at least 2" (msgsLen asAda ≥ 2)
    let asCarl ← get svc "/tickets/1" carl
    checkEq "carl sees ticket 200" asCarl.status 200
    check "carl never sees internal" (!anyInternal asCarl)
    checkEq "carl sees the public body only" (msgsLen asCarl) 1
    let sneak := Json.mkObj [("body", .str "I am an agent now."), ("internal", .bool true)]
    checkEq "customer internal 403" (← postJson svc "/tickets/1/messages" sneak carl).status 403
    let reply := Json.mkObj [("body", .str "Still broken.")]
    checkEq "customer reply 201" (← postJson svc "/tickets/1/messages" reply carl).status 201

  section_ "helpdesk who may write" do
    checkEq "gina on acme ticket ≡ missing"
      (← postJson svc "/tickets/1/messages" (Json.mkObj [("body", .str "hi")]) gina).status 404
    checkEq "carl cannot advance" (← postJson svc "/tickets/1/advance" (Json.mkObj []) carl).status 403
    checkEq "open → pending" (← postJson svc "/tickets/1/advance" (Json.mkObj []) ada).status 200
    checkEq "pending → solved" (← postJson svc "/tickets/1/advance" (Json.mkObj []) ada).status 200
    checkEq "solved → closed" (← postJson svc "/tickets/1/advance" (Json.mkObj []) ada).status 200
    checkEq "closed stays 409" (← postJson svc "/tickets/1/advance" (Json.mkObj []) ada).status 409
    checkEq "nobody posts on closed"
      (← postJson svc "/tickets/1/messages" (Json.mkObj [("body", .str "too late")]) carl).status 409
    checkEq "agent neither"
      (← postJson svc "/tickets/1/messages"
        (Json.mkObj [("body", .str "too late"), ("internal", .bool true)]) ada).status 409
    checkEq "inbound customer 403"
      (← postJson svc "/inbound" (Json.mkObj [
        ("messageId", .str "<x@acme>"), ("requester", Json.num 2),
        ("subject", .str "x"), ("body", .str "x")]) carl).status 403
    checkEq "cross-org requester 422"
      (← postJson svc "/inbound" (Json.mkObj [
        ("messageId", .str "<cross@acme>"), ("requester", Json.num 4),
        ("subject", .str "x"), ("body", .str "x")]) ada).status 422
    checkEq "wrapped ticket id 422" (← get svc s!"/tickets/{2^64 + 1}" ada).status 422

  section_ "helpdesk policy SQL" do
    let whoC : Who := ⟨UserId.ofNat! 2, OrgId.ofNat! 1, .customer⟩
    let whoA : Who := ⟨UserId.ofNat! 1, OrgId.ofNat! 1, .agent⟩
    let (sqlC, paramsC) := ticketGetSql whoC ⟨1⟩
    let (sqlA, paramsA) := ticketGetSql whoA ⟨1⟩
    check "customer filters org" ((sqlC.splitOn "org").length > 1)
    check "customer filters requester" ((sqlC.splitOn "requester").length > 1)
    check "customer binds org, requester, id" (paramsC.size ≥ 3)
    check "agent filters org" ((sqlA.splitOn "org").length > 1)
    IO.println s!"  customer get: {sqlC}  params {paramsC.size}"
    IO.println s!"  agent get:    {sqlA}  params {paramsA.size}"

  dc.close

end Tests.HelpdeskHttp
