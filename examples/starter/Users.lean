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
