import LeanApi
import LeanApi.Native
import TestsNative.AuthChecks

open Lean LeanApi LeanDb Ontology Contract
namespace Checks
structure Item where
  label : String
  deriving LeanDb.Entity
schema% Database := Item

inductive Failure where
  | denied
  deriving Repr, BEq

def errorCodec : Codec Failure where
  schema := .variant [("denied", .unit)]
  encode _ := JsonWire.tagged "denied" .null
  decode value := do
    JsonWire.object ["tag", "value"] value
    let _ ← Codec.field "value" Codec.unit value
    let tag ← JsonWire.stringField "tag" value
    if tag == "denied" then pure .denied else Validation.fail "decode.unknown_tag"

def must (result : Except ε α) : IO α := match result with
  | .ok value => pure value
  | .error _ => throw (IO.userError "fixture setup failed")

def check (condition : Bool) (label : String) : IO Unit :=
  unless condition do throw (IO.userError label)

private def inputCodec : Validation (Codec String) := Codec.record ⟨"checks", "Input"⟩ <|
  (RecordFields.pure id).apply (RecordFields.field "label" Codec.string id)

def operation : Validation (Operation .command String Nat Failure) := do
  Operation.create .command ⟨"checks", "add", "1"⟩ (← inputCodec) Codec.nat errorCodec

def command (env : Env) (req : Req) (label : String) :
    {σ : Type} → Txn σ Database (CallError Failure) Nat := do
  if req.header? "x-test-auth" == some "missing" then Txn.throw .unauthenticated
  if req.header? "x-test-auth" == some "forbidden" then Txn.throw .forbidden
  discard <| Txn.insertNew (α := Item) (Checked.of ⟨label⟩ (by first | trivial | exact ⟨rfl, trivial⟩))
  if label == "abort" then Txn.throw (.domain .denied)
  -- Exact value past JavaScript's safe integer; the fixture checks wire parity.
  pure (9007199254740993 + env.now)
end Checks

namespace NativeFixture

def run (execute : LeanApi.Native.Published.Executor Checks.Database := LeanApi.DbProg.execWithEnv) : IO Unit := do
  AuthChecks.run
  let codecs ← Checks.must Contract.Http.codecs
  let op ← Checks.must Checks.operation
  let publication := LeanApi.Native.TrustedAdapter.command codecs op Checks.command
    (fun _ => 409) { path := "/api/checks/add", maxBodyBytes := some 4096 }
  let queryOp ← Checks.must (Operation.create .query ⟨"checks", "list", "1"⟩ Codec.unit
    (Ontology.disclosureCodec (Codec.list Codec.string)) Checks.errorCodec)
  let read := LeanApi.Native.TrustedAdapter.query codecs queryOp (fun _ req _ => do
    if req.header? "x-test-visibility" != some "allowed" then return .ok .hidden
    let rows ← Read.all (Query.from Checks.Item (s := Checks.Database))
    return .ok (.visible (rows.map (·.val.label)))) (fun _ => 409) {path := "/api/checks/list"}
  let .ok app := LeanApi.Native.Application.create [publication, read]
    | throw (IO.userError "application allowlist")
  Checks.check (app.manifest.length == 2) "explicit allowlist"
  Checks.check (LeanApi.Native.Application.create [publication, publication]).toOption.isNone "duplicate allowlist"
  let token ← Tokens.generate
  IO.FS.createDirAll ".lake/test-db"
  let dc ← DbConns.open s!".lake/test-db/contract-{token}.sqlite" (IsSchema.specs Checks.Database) 1
  try
    let service := app.service dc (fresh := pure { now := 7 }) (execute := execute)
    let call := fun (wire : WireRequest) (headers : List (String × String)) =>
      LeanApi.Test.postJson service "/api/checks/add" (Contract.Http.encodeRequest codecs wire) headers
    let wire : WireRequest := ⟨op.identity, .command, op.inputCodec.encode "persisted"⟩
    let success ← call wire []
    Checks.check (success.status == 200) "real HTTP success"
    Checks.check (success.header? "cache-control" == some "private, no-store") "protected no-store"
    let decoded ← Checks.must (Contract.Http.decodeResponse codecs [publication.errorStatus] wire
      success.status (← Checks.must (Json.parse success.body)))
    let .success value := decoded | throw (IO.userError "success envelope")
    Checks.check ((op.outputCodec.decode value).toOption == some 9007199254741000) "exact large output"
    let badWire : WireRequest := { wire with input := op.inputCodec.encode "abort" }
    let domain ← call badWire []
    Checks.check (domain.status == 409) "non-2xx typed domain error"
    let decoded ← Checks.must (Contract.Http.decodeResponse codecs [publication.errorStatus] badWire
      domain.status (← Checks.must (Json.parse domain.body)))
    let .domainError value := decoded | throw (IO.userError "domain envelope")
    Checks.check ((op.errorCodec.decode value).toOption == some .denied) "typed domain decoding"
    let missing ← call wire [("x-test-auth", "missing")]
    Checks.check (missing.status == 401) "unauthenticated channel"
    let forbidden ← call wire [("x-test-auth", "forbidden")]
    Checks.check (forbidden.status == 403) "forbidden channel"
    let stale ← call { wire with operation := { wire.operation with version := "0" } } []
    Checks.check (stale.status == 409 && stale.body.contains '0') "version rejected"
    let wrongKind ← call { wire with kind := .query } []
    Checks.check (wrongKind.status == 400) "kind rejected before execution"
    let forged : WireRequest := { wire with input := .mkObj [("label", .str "tampered"), ("actor", .str "host")] }
    let invalid ← call forged []
    Checks.check (invalid.status == 400) "unknown injected input rejected"
    Checks.check ((← LeanApi.Test.request service "POST" "/api/checks/add" [] "{").status == 400) "malformed JSON"
    let oversized ← LeanApi.Test.request service "POST" "/api/checks/add" [] (String.ofList (List.replicate 4097 'x'))
    Checks.check (oversized.status == 413 && oversized.body == (Contract.Http.protocolResponse "request.body_too_large").compress)
      "buffering refusal preserves typed envelope"
    let manifest ← LeanApi.Test.get service "/api/manifest"
    Checks.check (manifest.status == 200 && manifest.body == (LeanApi.Publication.PublicOperation.manifest app.manifest).compress)
      "exact shared manifest bytes"
    let count ← Checks.must (← DbM.run dc.writer.conn (Read.run (Read.count (Query.from Checks.Item (s := Checks.Database)))))
    Checks.check (count.toOption == some 1) "aborts and boundary refusals leave persisted rows unchanged"
    let native : Transport IO := { send := fun request => do
      let reply ← call request []
      return Contract.Http.decodeResponse codecs [publication.errorStatus] request reply.status
        (← Checks.must (Json.parse reply.body)) }
    Checks.check ((← native.interpreter.call op "native").toOption == some 9007199254741000) "native client actual HTTP parity"
    let queryWire : WireRequest := ⟨queryOp.identity, .query, .null⟩
    let hidden ← LeanApi.Test.postJson service "/api/checks/list" (Contract.Http.encodeRequest codecs queryWire)
    let visible ← LeanApi.Test.postJson service "/api/checks/list" (Contract.Http.encodeRequest codecs queryWire)
      [("x-test-visibility", "allowed")]
    Checks.check (hidden.body == (Contract.Http.successResponse codecs queryOp.identity
      ((Ontology.disclosureCodec (Codec.list Codec.string)).encode .hidden)).compress)
      "hidden is canonical unit without guest data"
    Checks.check ((hidden.body.splitOn "persisted").length == 1) "hidden response excludes stored data"
    let .ok (.success names) := Contract.Http.decodeResponse codecs [read.errorStatus] queryWire visible.status
      (← Checks.must (Json.parse visible.body)) | throw (IO.userError "visible reply")
    let .ok (.visible labels) := queryOp.outputCodec.decode names | throw (IO.userError "visible decoder")
    Checks.check (labels == ["persisted", "native"]) "nonempty read projects actual persisted labels"
    let out : System.FilePath := ".lake/ddd-contract-client"
    app.emitClient codecs out (runtime := ".")
    let repeatOut := out / "repeat"
    app.emitClient codecs repeatOut (runtime := ".")
    for artifact in ["operations.mjs", "operations.d.ts", "operations.d.mts", "manifest.json"] do
      Checks.check ((← IO.FS.readBinFile (out / artifact)) == (← IO.FS.readBinFile (repeatOut / artifact)))
        s!"deterministic generated {artifact}"
    let preparations ← IO.mkRef 0
    let preparedPublication := LeanApi.Native.TrustedAdapter.preparedCommand codecs op
      (fun _ input => do
        unless (← dc.writer.conn.txDepth.get) == 0 do
          throw (IO.userError "preparation inside writer transaction")
        preparations.modify (· + 1)
        return .ok input)
      (fun env req _ prepared => do
        let output ← Checks.command env req prepared
        let receipt : Res.Cookie :=
          { name := "fixture_receipt", value := if prepared == "bad-cookie" then ";invalid" else "committed" }
        return (output, {cookies := [receipt]}))
      (fun _ => 409) {path := "/api/checks/prepared"}
    let .ok preparedApp := LeanApi.Native.Application.create [preparedPublication]
      | throw (IO.userError "prepared application allowlist")
    let preparedService := preparedApp.service dc (fresh := pure {now := 7}) (execute := execute)
    let preparedSuccess ← LeanApi.Test.postJson preparedService "/api/checks/prepared"
      (Contract.Http.encodeRequest codecs {wire with input := op.inputCodec.encode "prepared"})
    Checks.check (preparedSuccess.status == 200 && (preparedSuccess.headers.filter (·.1 == "set-cookie")).length == 1)
      "native preparation metadata issued on commit"
    let preparedAbort ← LeanApi.Test.postJson preparedService "/api/checks/prepared"
      (Contract.Http.encodeRequest codecs badWire)
    Checks.check (preparedAbort.status == 409 && (preparedAbort.headers.filter (·.1 == "set-cookie")).isEmpty)
      "late abort never issues prepared cookies"
    let invalidCookie ← LeanApi.Test.postJson preparedService "/api/checks/prepared"
      (Contract.Http.encodeRequest codecs {wire with input := op.inputCodec.encode "bad-cookie"})
    Checks.check (invalidCookie.status == 500 && invalidCookie.body ==
      (Contract.Http.protocolResponse "response.invalid_cookie").compress &&
      (invalidCookie.headers.filter (·.1 == "set-cookie")).isEmpty)
      "invalid native response metadata aborts without issuing cookies"
    let finalCount ← Checks.must (← DbM.run dc.writer.conn
      (Read.run (Read.count (Query.from Checks.Item (s := Checks.Database)))))
    Checks.check (finalCount.toOption == some 3 && (← preparations.get) == 3)
      "prepared abort restores every write; preparation runs exactly once outside writer"
    dc.close
    let databaseFault ← call wire []
    Checks.check (databaseFault.status == 500 && databaseFault.body ==
      (Contract.Http.protocolResponse "database.unavailable").compress) "real stopped database typed fault"
    IO.FS.writeFile (out / "fixture.json") (Json.mkObj [("success", ← Checks.must (Json.parse success.body)),
      ("database", ← Checks.must (Json.parse databaseFault.body)),
      ("hidden", ← Checks.must (Json.parse hidden.body)), ("visible", ← Checks.must (Json.parse visible.body)),
      ("domain", ← Checks.must (Json.parse domain.body)), ("decode", ← Checks.must (Json.parse invalid.body)),
      ("unauthenticated", ← Checks.must (Json.parse missing.body)), ("forbidden", ← Checks.must (Json.parse forbidden.body)),
      ("incompatible", ← Checks.must (Json.parse stale.body)), ("protocol", ← Checks.must (Json.parse wrongKind.body))]).compress
    let fault := LeanApi.Native.databaseReply (.io "private SQL/session/password detail")
    Checks.check (fault.status == 500 && fault.bodyText == (Contract.Http.protocolResponse "database.unavailable").compress)
      "database errors redacted"
    IO.println "PASS: native client / real HTTP framing / SQLite / exact shared Contract envelopes"
  finally dc.close

end NativeFixture
