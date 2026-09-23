import LeanApi

namespace Tests.Auth

open LeanApi LeanApi.Test Lean

def key : ByteArray := "0123456789abcdef0123456789abcdef".toUTF8
def pol : Jwt.Policy := { key, issuer := some "leanapi", audience := some "games" }
def now : Nat := 1_800_000_000

def claims (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("sub", .str "alice"), ("iss", .str "leanapi"), ("aud", .str "games"),
    ("iat", Json.num (now - 10 : Nat)), ("exp", Json.num (now + 600 : Nat))] ++ extra)

def rawToken (header payload : Json) (k : ByteArray := key) : String :=
  let h := LeanCrypto.Base64Url.encode header.compress.toUTF8
  let b := LeanCrypto.Base64Url.encode payload.compress.toUTF8
  s!"{h}.{b}.{LeanCrypto.Base64Url.encode (LeanCrypto.hmacSha256 k s!"{h}.{b}".toUTF8)}"

def isErr (e : Jwt.JwtError) (r : Except Jwt.JwtError Json) : Bool :=
  match r with | .error e' => e == e' | .ok _ => false

def run : TestM Unit := do
  section_ "JWT HS256" do
    let t := Jwt.sign key (claims)
    check "valid token" ((Jwt.verify pol now t).toOption.isSome)
    check "sub claim" (((Jwt.verify pol now t).toOption.bind fun c => (c.getObjValAs? String "sub").toOption) == some "alice")
    check "expired" (isErr .expired (Jwt.verify pol (now + 700) t))
    check "within leeway" ((Jwt.verify pol (now + 620) t).toOption.isSome)
    check "nbf in future" (isErr .notYetValid (Jwt.verify pol now (Jwt.sign key (claims [("nbf", Json.num (now + 100 : Nat))]))))
    check "iat in future" (isErr .issuedInFuture (Jwt.verify pol now (Jwt.sign key (claims [("iat", Json.num (now + 100 : Nat))]))))
    check "wrong issuer" (isErr .issuer (Jwt.verify pol now (Jwt.sign key (claims [("iss", .str "evil")]))))
    check "wrong audience" (isErr .audience (Jwt.verify pol now (Jwt.sign key (claims [("aud", .str "other")]))))
    check "audience array" ((Jwt.verify pol now (Jwt.sign key (claims [("aud", Json.arr #[.str "x", .str "games"])]))).toOption.isSome)
    check "missing exp" (isErr (.missingClaim "exp") (Jwt.verify pol now (Jwt.sign key (Json.mkObj [("sub", .str "a"), ("iss", .str "leanapi"), ("aud", .str "games")]))))
    check "wrong key" (isErr .signature (Jwt.verify pol now (Jwt.sign "ffffffffffffffffffffffffffffffff".toUTF8 claims)))
    let parts := t.splitOn "."
    let tampered := s!"{parts[0]!}.{LeanCrypto.Base64Url.encode (claims [("sub", .str "bob")]).compress.toUTF8}.{parts[2]!}"
    check "tampered payload" (isErr .signature (Jwt.verify pol now tampered))
    let noneTok := s!"{LeanCrypto.Base64Url.encode "{\"alg\":\"none\"}".toUTF8}.{parts[1]!}."
    check "alg none rejected" (isErr (.algorithm "none") (Jwt.verify pol now noneTok))
    check "alg HS512 rejected" (isErr (.algorithm "HS512") (Jwt.verify pol now (rawToken (Json.mkObj [("alg", .str "HS512")]) claims)))
    check "alg RS256 rejected" (isErr (.algorithm "RS256") (Jwt.verify pol now (rawToken (Json.mkObj [("alg", .str "RS256")]) claims)))
    check "crit rejected" (!(Jwt.verify pol now (rawToken (Json.mkObj [("alg", .str "HS256"), ("crit", Json.arr #[.str "x"])]) claims)).toOption.isSome)
    check "two segments" (!(Jwt.verify pol now "a.b").toOption.isSome)
    check "padded base64 rejected" (!(Jwt.verify pol now (t ++ "=")).toOption.isSome)
    check "weak key refused" (isErr .weakKey (Jwt.verify { pol with key := "short".toUTF8 } now t))
    check "maxAge" (!(Jwt.verify { pol with maxAge := some 60 } now t).toOption.isSome)

  section_ "JWT bearer authenticator" do
    let auth := jwtBearer pol (fun c => pure (c.getObjValAs? String "sub").toOption) (pure now)
    let svc := Service.ofRouter (Router.build! [Route.get "/me" (requireAuth auth fun who _ => pure (Res.text who))])
    checkEq "jwt ok" (← get svc "/me" [("Authorization", s!"Bearer {Jwt.sign key claims}")]).body "alice"
    checkEq "jwt expired 401" (← get svc "/me" [("Authorization", s!"Bearer {Jwt.sign key (claims [("exp", Json.num (now - 100 : Nat))])}")]).status 401
    checkEq "no header 401" (← get svc "/me").status 401

  section_ "opaque tokens and passwords" do
    let t1 ← Tokens.generate
    let t2 ← Tokens.generate
    check "tokens distinct" (t1 != t2)
    checkEq "token length (256 bits base64url)" t1.length 43
    checkEq "digest is hex sha256" (Tokens.digest "abc") "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
    let table ← IO.mkRef [(Tokens.digest t1, "alice")]
    let lookups ← IO.mkRef ([] : List String)
    let auth := Tokens.bearerAuth fun d => do lookups.modify (d :: ·); return (← table.get).lookup d
    let svc := Service.ofRouter (Router.build! [Route.get "/me" (requireAuth auth fun who _ => pure (Res.text who))])
    checkEq "opaque ok" (← get svc "/me" [("Authorization", s!"Bearer {t1}")]).body "alice"
    checkEq "opaque unknown 401" (← get svc "/me" [("Authorization", s!"Bearer {t2}")]).status 401
    check "lookup by digest, never raw" ((← lookups.get).all fun d => d.length == 64 && d != t1 && d != t2)
    let fast : LeanCrypto.Password.Params := { logN := 10 }
    let stored ← LeanCrypto.Password.hash "hunter2" fast
    let dummy ← dummyHashFor fast
    let users := [("alice", ("alice", stored))]
    let basicA := basicWithPasswords (fun u => pure (users.lookup u)) dummy
    let svc := Service.ofRouter (Router.build! [Route.get "/me" (requireAuth basicA fun who _ => pure (Res.text who))])
    let hdr (u p : String) := [("Authorization", "Basic " ++ Base64.encode s!"{u}:{p}".toUTF8)]
    checkEq "basic scrypt ok" (← get svc "/me" (hdr "alice" "hunter2")).body "alice"
    checkEq "basic wrong pw" (← get svc "/me" (hdr "alice" "hunter3")).status 401
    checkEq "basic unknown user" (← get svc "/me" (hdr "mallory" "hunter2")).status 401
    check "stored hash is not the password" (!stored.contains "hunter2" && stored.startsWith "$scrypt$")

end Tests.Auth
