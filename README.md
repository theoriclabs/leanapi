# LeanAPI

**A fully functional API server for Lean 4. Think of it as Express or FastAPI, for Lean.**

Routes, middleware, authentication, CORS, headers, query parameters, JSON bodies with validation: the usual things, with handlers that are plain Lean functions. A handler's arguments say where each input comes from, and LeanAPI decodes and validates them before your code runs.

> **Status: v0.1.0, the first release.** Usable, and experimental: APIs may change.

## Features

- **Routing:** path parameters (`/items/{item_id}`, or typed like `{id:nat}`), route groups, `404` vs `405` with `Allow`, automatic `HEAD` and `OPTIONS`. Conflicting routes are rejected at compile time.
- **Requests:** path and query parameters, headers, cookies, JSON and form bodies, multipart uploads. Invalid input is a `422` that names the field (`body.price`, `query.limit`), as in FastAPI.
- **Responses:** JSON, text, `201 Created` with `Location`, `204 No Content`, ETags and conditional requests, cookies. Errors are RFC 9457 `application/problem+json`, and an exception is a `500` that reveals nothing.
- **Middleware:** `cors`, `accessLog`, `requestId`, `recover`, `timeout`, `rateLimit`, `securityHeaders`, `health`, `trustedProxy`, or your own.
- **Auth:** bearer tokens, Basic auth, session cookies, HS256 JWT, and password hashing (scrypt). A missing or bad credential is a `401` with `WWW-Authenticate`.
- **Also:** Server-Sent Events, OpenAPI 3.1 with a `/docs` page, graceful shutdown, and an in-process test client.

## Install

In your `lakefile.toml`:

```toml
[[require]]
name = "leanapi"
git = "https://github.com/theoriclabs/leanapi"
rev = "v0.1.0"
```

You need:
- the toolchain `leanprover/lean4:v4.33.0`;
- OpenSSL 3 (`brew install openssl@3`, or `apt install libssl-dev`).

> The `leanapi` repository and its dependencies are currently private; you need read access.

## Hello World

<!-- file: examples/starter/Hello.lean -->
```lean
import LeanApi
open LeanApi

def hello : Text := ⟨"Hello World!"⟩

def app : Api Unit := api! [.get "/" hello]

def main : IO Unit := app.listen 3000
```

```text
$ lake exe hello
listening on http://127.0.0.1:3000

$ curl localhost:3000
Hello World!
```

## Path parameters, query parameters and JSON bodies

<!-- file: examples/starter/Items.lean -->
```lean
import LeanApi
open LeanApi Lean

structure Item where
  name : String
  price : Float
  isOffer : Option Bool

instance : FromBody Item := .record (Item.mk <$> .req "name" <*> .req "price" <*> .opt "is_offer")

def readRoot : Json := json% {"Hello": "World"}

def readItem (itemId : Path Int) (q : QueryParam "q" (Option String)) : Json :=
  json% {"item_id": $(itemId.val), "q": $(q.val)}

def updateItem (itemId : Path Int) (item : Body Item) : Json :=
  json% {"item_name": $(item.val.name), "item_id": $(itemId.val)}

def app : Api Unit := api! [
  .get "/"                readRoot,
  .get "/items/{item_id}" readItem,
  .put "/items/{item_id}" updateItem ]

def main : IO Unit := app.listen 8000
```

Each handler's arguments say where its inputs come from: `Path` (the `{item_id}` segment), `QueryParam "q"`, `Body`. They arrive already decoded, and the handler just returns its answer. Invalid input never reaches it:

```text
$ lake exe items
$ curl 'localhost:8000/items/5?q=somequery'
{"item_id":5,"q":"somequery"}

$ curl -X PUT localhost:8000/items/5 -H 'content-type: application/json' -d '{"name":"Foo","price":42.5}'
{"item_id":5,"item_name":"Foo"}

$ curl -X PUT localhost:8000/items/5 -H 'content-type: application/json' -d '{"name":"Foo"}'
{"detail":"request validation failed","errors":[{"loc":"body.price","msg":"field required"}],"status":422,...}

$ curl localhost:8000/items/abc
{"detail":"request validation failed","errors":[{"loc":"path.item_id","msg":"expected an integer"}],"status":422,...}
```

## Middleware, headers and auth

A small app: CORS and a request log as middleware, a list with a `?limit=` query parameter, a `POST` with a JSON body, and a route that needs a bearer token.

<!-- file: examples/starter/Users.lean -->
```lean
import LeanApi
open LeanApi Lean

structure User where
  id : Nat
  name : String
  deriving ToJson

structure State where
  users : Array User := #[⟨1, "Ada"⟩]
  tokens : List (String × Nat) := [("secret", 1)]

-- `Authorization: Bearer secret` is Ada; anything else is a 401.
instance : Authenticates State User :=
  .sessions fun s token => (s.tokens.lookup token).bind fun id => s.users.find? (·.id == id)

structure NewUser where
  name : String

instance : FromBody NewUser := .record (NewUser.mk <$> .req "name")

def listUsers (limit : QueryParam "limit" (Option Nat)) : Reads State (List User) :=
  fun s => s.users.toList.take (limit.val.getD 10)

def createUser (body : Body NewUser) : Writes State (Created User) := fun s =>
  let user : User := ⟨s.users.size + 1, body.val.name⟩
  ({ s with users := s.users.push user }, { val := user, location := some s!"/users/{user.id}" })

def me (user : Auth User) (agent : Header "user-agent" (Option String)) : Json :=
  json% {"id": $(user.val.id), "name": $(user.val.name), "agent": $(agent.val)}

def app : Api State := api! [
  .get  "/users"    listUsers,
  .post "/users"    createUser,
  .get  "/users/me" me ]

def main : IO Unit :=
  app.listenWith {} 3000 (stack := Stack.of [
    cors { origins := .list ["http://localhost:5173"] },
    accessLog ])
```

The types do the work:
- **`Auth User`** makes `/users/me` require a valid token. Nothing else in the handler checks it.
- **`Reads State`** can only read the state and **`Writes State`** can change it. A `GET` handler that writes doesn't compile.
- **`Created User`** answers `201` with the `Location` header.

```text
$ lake exe users
$ curl -i localhost:3000/users/me
HTTP/1.1 401 Unauthorized
www-authenticate: Bearer realm="api"
...

$ curl localhost:3000/users/me -H 'authorization: Bearer secret'
{"agent":"curl/8.7.1","id":1,"name":"Ada"}

$ curl -X POST localhost:3000/users -H 'content-type: application/json' -d '{}'
{"detail":"request validation failed","errors":[{"loc":"body.name","msg":"field required"}],"status":422,...}

$ curl 'localhost:3000/users?limit=x'
{"detail":"request validation failed","errors":[{"loc":"query.limit","msg":"expected a natural number"}],"status":422,...}
```

For a bigger app (sign-up and login, sessions in cookies, ETags, pagination, CORS with credentials), see [`examples/notes`](examples/notes/Notes/App.lean).

## Run the examples

```bash
lake exe hello        # Hello World, on :3000
lake exe items        # path, query and body, on :8000
lake exe users        # middleware, headers and auth, on :3000
./examples/starter/smoke.sh   # starts each one and checks the answers above
```

## Not there yet

- **Throughput is modest.** LeanAPI runs on Lean's built-in `Std.Http` server: roughly 2,000–3,500 requests per second for a trivial route on a laptop.
- **OpenAPI is written by hand.** Routes carry a description, and LeanAPI serves the document and a `/docs` page. It isn't generated from handler types yet.
- **No WebSockets here.** They live in a separate library.

## Build and test

```bash
lake build
lake build leanapi_tests && ./.lake/build/bin/leanapi_tests
./scripts/check_readme.sh     # every Lean example in this README compiles, and matches examples/starter
```

## License

[Business Source License 1.1](LICENSE), converting to MIT four years after each version is published. Copyright (c) 2026 Theoriclabs, Inc.

- **Free production use** for organizations with 100 or fewer people and US $100 million or less in annual revenue (affiliates included).
- **Not permitted without a commercial license:** offering a Competing Service. That means LeanAPI itself, or a product whose main value is LeanAPI, sold as a hosted backend platform or embedded in a framework or developer tool. Building and running your own applications with LeanAPI, including ones you sell, is not a Competing Service.
- **Always allowed:** non-production use (development, testing, evaluation), copying, modifying and redistributing under the same license.
- **Commercial licenses:** team@theoric.com.
