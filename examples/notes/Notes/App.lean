/-
  Notes: a small CRUD-ish app using every M1 feature.

    POST   /api/users                 {"name","password"}      register (form or JSON)
    POST   /api/sessions              Basic auth → {"token"}   login, also sets a cookie
    GET    /api/notes?page=&per=      list my notes
    POST   /api/notes                 {"title","body","tags"?}
    GET    /api/notes/{id:nat}
    PATCH  /api/notes/{id:nat}        {"title"?,"body"?}  If-Match: "<rev>"
    DELETE /api/notes/{id:nat}

  Auth: bearer token, or the `sid` cookie. Passwords here are compared
  directly because M1 has no crypto; `examples/private-games` uses the
  crypto dependency. Store: an in-memory map under `Std.Mutex`.
-/
import LeanApi
import Std.Sync.Mutex

namespace Notes

open LeanApi Lean

structure Title where
  raw : String
  deriving Repr, BEq

instance : SmartCtor Title String where
  make s :=
    let t := s.trimAscii.toString
    if t.isEmpty then .error "title must be nonempty"
    else if t.length > 200 then .error "title must be at most 200 characters"
    else .ok ⟨t⟩
  raw := (·.raw)

structure Note where
  id : Nat
  owner : String
  title : Title
  body : String
  rev : Nat := 1

def Note.toJson (n : Note) : Json :=
  Json.mkObj [("id", Json.num n.id), ("title", .str n.title.raw), ("body", .str n.body), ("rev", Json.num n.rev)]

structure Store where
  users : List (String × String) := []
  tokens : List (String × String) := []
  notes : Array Note := #[]
  nextId : Nat := 1

abbrev Db := Std.Mutex Store

def Db.new : IO Db := Std.Mutex.new {}

def atomically (db : Db) (f : Store → Store × α) : IO α :=
  db.atomically do
    let s ← get
    let (s', a) := f s
    set s'
    return a

def read (db : Db) (f : Store → α) : IO α := db.atomically do return f (← get)

def auth (db : Db) : Authenticator String :=
  let lookup (t : String) : IO (Option String) := read db fun s => s.tokens.lookup t
  (bearer lookup).orElse (sessionCookie "sid" lookup)

def ownNote (s : Store) (who : String) (id : Nat) : Option Note :=
  s.notes.find? fun n => n.id == id && n.owner == who

def etag (n : Note) : String := s!"\"{n.rev}\""

structure Register where
  name : String
  password : String

def decodeRegister : Extract Register := fun r =>
  if r.contentType? == some "application/x-www-form-urlencoded" then
    (fun n p => ⟨n, p⟩) <$> Extract.form "name" <*> Extract.form "password" |>.run r
  else do
    let j ← Extract.rawJson r
    let (n, p) ← both (field "body" j "name") (field "body" j "password")
    return ⟨n, p⟩

def routes (db : Db) : List Route :=
  let authed := requireAuth (auth db)
  group "/api" <| routes! [
    Route.post "/users" (requireContentType ["application/json", "application/x-www-form-urlencoded"] <|
      handle decodeRegister fun u => do
        if u.name.isEmpty || u.password.length < 4 then
          return (Problem.make 422 (some "name required, password at least 4 characters")).toRes
        let ok ← atomically db fun s =>
          if (s.users.lookup u.name).isSome then (s, false) else ({ s with users := (u.name, u.password) :: s.users }, true)
        if ok then return Res.created (Json.mkObj [("name", .str u.name)])
        else return (Problem.conflict "name taken").toRes),
    Route.post "/sessions" (requireAuth
      (basic fun u p => read db fun s => if s.users.lookup u == some p then some u else none)
      fun who _ => do
        let bytes ← IO.getRandomBytes 24
        let tok := Base64.encodeUrl bytes
        atomically db fun s => ({ s with tokens := (tok, who) :: s.tokens }, ())
        return (Res.created (Json.mkObj [("token", .str tok)])).setCookie { name := "sid", value := tok }),
    Route.get "/notes" (authed fun who =>
      handle ((·, ·) <$> Extract.queryD "page" 1 <*> Extract.queryD "per" 20) fun (page, per) => do
        if page == 0 || per == 0 || per > 100 then
          return (FieldError.problem [⟨"query.per", "page ≥ 1, 1 ≤ per ≤ 100"⟩]).toRes
        let mine ← read db fun s => s.notes.filter (·.owner == who)
        let items := (mine.toList.drop ((page - 1) * per)).take per
        return Res.ok (Json.mkObj [("items", Json.arr (items.map Note.toJson).toArray),
                                   ("total", Json.num mine.size), ("page", Json.num page)])),
    Route.post "/notes" (authed fun who => handleJson (fun r => do
        let j ← Extract.rawJson r
        let (t, b) ← both (field (α := Title) "body" j "title") (fieldD "body" j "body" "")
        return (t, b)) fun (t, b) => do
      let n ← atomically db fun s =>
        let n : Note := { id := s.nextId, owner := who, title := t, body := b }
        ({ s with notes := s.notes.push n, nextId := s.nextId + 1 }, n)
      return (Res.created n.toJson s!"/api/notes/{n.id}").setHeader "etag" (etag n)),
    Route.get "/notes/{id:nat}" (authed fun who => handle (Extract.path "id") fun id => do
      match ← read db (ownNote · who id) with
      -- someone else's note is indistinguishable from a missing one
      | none => return Problem.notFound.toRes
      | some n =>
        let r := (Res.ok n.toJson).setHeader "etag" (etag n)
        return r),
    (Route.patch "/notes/{id:nat}" (authed fun who => handleJson (fun r => do
        let id ← Extract.path (α := Nat) "id" r
        let ifMatch ← Extract.headerOpt (α := String) "if-match" r
        let j ← Extract.rawJson r
        let (t, b) ← both (fieldOpt (α := Title) "body" j "title") (fieldOpt (α := String) "body" j "body")
        return (id, ifMatch, t, b)) fun (id, ifMatch, t, b) => do
      let out ← atomically db fun s =>
        match ownNote s who id with
        | none => (s, Sum.inl Problem.notFound)
        | some n =>
          if ifMatch.isSome && ifMatch != some (etag n) then (s, .inl (Problem.make 412 (some "note changed")))
          else
            let n' := { n with title := t.getD n.title, body := b.getD n.body, rev := n.rev + 1 }
            ({ s with notes := s.notes.map fun x => if x.id == id then n' else x }, .inr n')
      match out with
      | .inl p => return p.toRes
      | .inr n => return (Res.ok n.toJson).setHeader "etag" (etag n))).limit (64 * 1024),
    Route.delete "/notes/{id:nat}" (authed fun who => handle (Extract.path "id") fun id => do
      let ok ← atomically db fun s =>
        match ownNote s who id with
        | none => (s, false)
        | some _ => ({ s with notes := s.notes.filter (·.id != id) }, true)
      return if ok then Res.empty 204 else Problem.notFound.toRes)
  ]

def stack (log : String → IO Unit := IO.eprintln) : Stack := Stack.of [
  recover log, requestId, accessLog log, health, securityHeaders,
  cors { origins := .list ["http://localhost:5173"], credentials := true },
  trustedProxy ["127.0.0.1"], timeout 10000]

def service (db : Db) (log : String → IO Unit := IO.eprintln) : Service :=
  Service.ofRouter (Router.build! (routes db)) (stack log)

end Notes
