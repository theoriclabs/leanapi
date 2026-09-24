/-
  LAPI-10: retry fingerprints computed by the framework.
-/
import PrivateGames.DbApi
import Tests.Games

namespace Tests.Idempotency

open LeanApi LeanApi.Test Lean PrivateGames PrivateGames.App PrivateGames.Storage Tests.Games

private def req (m : Method) (target : String) (hs : List (String × String) := []) (body : String := "")
    (params : List (String × String) := []) : Req :=
  { Req.mk' m target (hs.map fun (k, v) => (k.toLower, v)) body.toUTF8 with params }

private def fp (op : String) (declared : List String) (r : Req) : String :=
  Retry.fingerprintOf op declared r

/-! A test endpoint that declares a header: adding it to the signature
    changes the fingerprint, with no change to the endpoint's code. -/

def plain (k : Idempotency) : Nat := (k.retry.map (·.fingerprint.length)).getD 0
def withHeader (_h : Header "x-tenant" (Option String)) (k : Idempotency) : String :=
  (k.retry.map (·.fingerprint)).getD ""
def plainFp (k : Idempotency) : String := (k.retry.map (·.fingerprint)).getD ""

def run : TestM Unit := do
  section_ "LAPI-10: canonical form" do
    let j1 := req .post "/games" [("content-type", "application/json")] "{\"a\":1,\"b\":[2,3]}"
    let j2 := req .post "/games" [("content-type", "application/json")] "{ \"b\" : [2, 3],\n \"a\": 1 }"
    checkEq "JSON key order and whitespace do not matter" (fp "POST /games" [] j1) (fp "POST /games" [] j2)
    let j3 := req .post "/games" [("content-type", "application/json")] "{\"a\":1,\"b\":[3,2]}"
    check "JSON content matters" (fp "POST /games" [] j1 != fp "POST /games" [] j3)
    checkEq "query order does not matter"
      (fp "GET /x" [] (req .get "/x?a=1&b=2")) (fp "GET /x" [] (req .get "/x?b=2&a=1"))
    check "query value matters" (fp "GET /x" [] (req .get "/x?a=1") != fp "GET /x" [] (req .get "/x?a=2"))
    check "versioned" ((fp "GET /x" [] (req .get "/x")).startsWith "v1:")
    check "endpoint identity matters" (fp "POST /a" [] j1 != fp "POST /b" [] j1)
    let k1 := req .post "/x" [("idempotency-key", "a")]
    let k2 := req .post "/x" [("idempotency-key", "b")]
    checkEq "the key itself is not part of the fingerprint" (fp "POST /x" [] k1) (fp "POST /x" [] k2)
    let other := req .post "/x" [("x-noise", "1")]
    checkEq "undeclared headers are not part of it" (fp "POST /x" [] other) (fp "POST /x" [] (req .post "/x"))

  section_ "LAPI-10: each keyed private-games input changes the fingerprint" do
    let json := [("content-type", "application/json")]
    let base (extra : List (String × String)) body params :=
      req .post "/games/1/moves" (json ++ [("if-match", "\"0\"")] ++ extra) body params
    let op := "POST /games/{id:nat}/moves"
    let b := fp op [] (base [] "{\"cell\":4}" [("id", "1")])
    check "path parameter" (b != fp op [] (base [] "{\"cell\":4}" [("id", "2")]))
    check "body field" (b != fp op [] (base [] "{\"cell\":5}" [("id", "1")]))
    check "If-Match" (b != fp op [] (req .post "/games/1/moves" (json ++ [("if-match", "\"1\"")]) "{\"cell\":4}" [("id", "1")]))
    let o := "POST /games"
    let ob := fp o [] (req .post "/games" json "{\"opponent\":2}")
    check "openGame: opponent" (ob != fp o [] (req .post "/games" json "{\"opponent\":3}"))
    check "openGame: minutes (a field the old string had only with a default)"
      (ob != fp o [] (req .post "/games" json "{\"opponent\":2,\"minutes\":5}"))

  section_ "LAPI-10: a declared header is part of the fingerprint, by signature alone" do
    let api : Api Unit := api! [.post "/p" plainFp, .post "/h" withHeader]
    let svc := api.service (Store.ofMutex (← Std.Mutex.new ()))
    let call (path tenant : String) := do
      let r ← request svc "POST" path [("Idempotency-Key", "k"), ("X-Tenant", tenant)]
      pure r.body
    check "undeclared: tenant ignored" ((← call "/p" "a") == (← call "/p" "b"))
    check "declared: tenant changes it" ((← call "/h" "a") != (← call "/h" "b"))

  section_ "LAPI-10: receipts written before the change still replay (v0)" do
    let e ← freshEnvFor .dbapi "v0-receipts"
    let (_, carol) ← signup e.svc "v0carol"
    let (daveId, _) ← signup e.svc "v0dave"
    -- A keyed open, and its receipt rewritten as the pre-LAPI-10 code stored it:
    -- the short operation name and the hand-built fingerprint.
    let r1 ← openGame e.svc carol daveId [("Idempotency-Key", "old")]
    checkEq "open 201" r1.status 201
    let hex (s : String) := LeanCrypto.Hex.encode (LeanCrypto.sha256 s.toUTF8)
    let _ ← LeanDb.DbM.run e.rt.writeConn (LeanDb.untrackedSqlite fun db =>
      db.exec s!"UPDATE receipt_row SET op = 'openGame', fingerprint = '{hex s!"openGame|{daveId}|10"}' WHERE key = 'old'")
    let r2 ← openGame e.svc carol daveId [("Idempotency-Key", "old")]
    checkEq "v0 receipt: replayed" (r2.header? "idempotent-replayed") (some "true")
    checkEq "v0 receipt: same body" r2.body r1.body
    let diff ← postJson e.svc "/games" (Json.mkObj [("opponent", Json.num daveId), ("minutes", Json.num 5)])
      [bearer carol, ("Idempotency-Key", "old")]
    checkEq "v0 receipt, different request: 422" diff.status 422
    checkEq "only one game" (jnat (← get e.svc "/games" [bearer carol]) "total") (some 1)
    e.close

end Tests.Idempotency
