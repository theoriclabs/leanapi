/-
  LAPI-02 (read half): endpoints over LeanDB read programs, served by
  `DbApi.service` against SQLite, with the laws of `Endpoint.lean`
  instantiated for them.
-/
import LeanApi

namespace Tests.DbEndpoint

open LeanApi LeanApi.Test Lean LeanDb

/-! ## A test schema: teams, members (unique name, a reference), sessions -/

structure Team where
  name : String
  deriving Repr, LeanDb.Entity

structure Member where
  name : String
  team : Ref Team
  deriving Repr, LeanDb.Entity

structure Session where
  token : String
  member : Ref Member
  deriving Repr, LeanDb.Entity

unique% Member.byName := name
unique% Session.byToken := token

schema% App := Team, Member, Session

/-! ## Endpoints -/

structure Me where
  id : LeanDb.Id Member
  team : LeanDb.Id Team

/-- A bearer token is a session row; the actor is its member, with the team. -/
def lookupSession (t : String) : Read App (Option Me) := do
  match ← Read.lookup Session Session.Unique.byToken t with
  | none => pure none
  | some sess =>
    match ← Read.get Member sess.val.member with
    | none => pure none
    | some m => pure (some ⟨m.id, m.val.team⟩)

instance : AuthenticatesDb App Me := AuthenticatesDb.sessions lookupSession

structure MemberView where
  id : Int
  name : String
  deriving ToJson

/-- A teammate by id. Members of other teams are indistinguishable from
    missing ones. -/
def getMember (me : Auth Me) (id : Path Nat) : Read App (Except NotFound MemberView) := do
  match ← Read.get Member ⟨Int64.ofNat id.val⟩ with
  | some m =>
    if m.val.team == me.val.team then pure (.ok ⟨m.id.toInt64.toInt, m.val.name⟩)
    else pure (.error ⟨⟩)
  | none => pure (.error ⟨⟩)

/-- My team's members: the first page of names and the total, from one
    snapshot. -/
def myTeam (me : Auth Me) : Read App (Paged String) := do
  let page ← Read.page ((Query.from Member (s := App)).where' (fun r => r.val.team == me.val.team))
    { limit := some 10 }
  pure ⟨page.items.map (·.val.name), page.total, 1⟩

structure NameQ where
  name : String

instance : FromQuery NameQ where
  fromQuery r := NameQ.mk <$> Extract.query "name" r

structure Taken where
  taken : Bool
  deriving ToJson

/-- Unauthenticated: is a name taken? -/
def nameTaken (n : QueryParams NameQ) : Read App Taken :=
  (fun m => ⟨m.isSome⟩) <$> Read.lookup Member Member.Unique.byName n.val.name

/-! ### Writes: transaction programs -/

structure NewMember where
  name : String

instance : FromBody NewMember := FromBody.record (NewMember.mk <$> Fields.req "name")

/-- Why joining can fail: the failure type is the schema's, mapped to a
    status by `ToProblem`. -/
inductive JoinError where
  | taken
  | noTeam
  | limit

instance : ToProblem JoinError where
  status
    | .taken => ⟨409, by decide⟩
    | .noTeam => ⟨422, by decide⟩
    | .limit => ⟨409, by decide⟩
  detail
    | .taken => some "name taken"
    | .noTeam => some "team is gone"
    | .limit => some "team is full"

private def checkedMember (m : Member) : Checked Member := Checked.of m trivial

/-- Add a member to my team. A duplicate name is the schema's `.duplicate`,
    turned into 409. More than 3 members aborts *after* the insert: the
    insert must not survive. -/
def join (me : Auth Me) (b : Body NewMember) : Tx App JoinError (Created MemberView) := do
  let row ← Txn.orAbort (Txn.insert Member (checkedMember ⟨b.val.name, me.val.team⟩)) fun
    | .duplicate _ _ => JoinError.taken
    | .missingRef _ => JoinError.noTeam
  let n ← Txn.liftRead (Read.count ((Query.from Member (s := App)).where' (fun r => r.val.team == me.val.team)))
  if n > 3 then Txn.throw .limit
  pure ⟨⟨row.id.toInt64.toInt, row.val.name⟩, s!"/members/{row.id.toInt64.toInt}"⟩

/-! ### LeanDB's failure types answered directly (LAPI-03 defaults) -/

structure Signup where
  name : String
  team : Nat

instance : FromBody Signup := FromBody.record (Signup.mk <$> Fields.req "name" <*> Fields.req "team")

/-- Unauthenticated signup that exposes LeanDB's own failure type. -/
def signup (b : Body Signup) : Tx App (InsertError Member) (Created MemberView) := do
  let row ← Txn.orAbort (Txn.insert Member (checkedMember ⟨b.val.name, ⟨Int64.ofNat b.val.team⟩⟩)) fun e => e
  pure ⟨⟨row.id.toInt64.toInt, row.val.name⟩, s!"/members/{row.id.toInt64.toInt}"⟩

/-- Remove a team: `.gone` → 404, `.restricted` → 409 without saying by what. -/
def dropTeam (id : Path Nat) : Tx App (DeleteError App Team) NoContent := do
  let _ ← Txn.orAbort (Txn.delete Team ⟨Int64.ofNat id.val⟩) fun e => e
  pure ⟨⟩

def api : DbApi App := api! [
  .get "/members/{id}" getMember,
  .get "/team" myTeam,
  .get "/names" nameTaken,
  .post "/members" join,
  .post "/signup" signup,
  .delete "/teams/{id}" dropTeam
]

/-! ## Compile time -/

/-- The effect of a read program is `reads`, of a transaction `writes`. -/
example : Handler.effect (σ := DbState App) (τ := type_of% getMember) = .reads := rfl
example : Handler.effect (σ := DbState App) (τ := type_of% join) = .writes := rfl

-- A GET whose handler returns a transaction does not build.
/-- error: could not synthesize default value for parameter 'safe' using tactics
---
error: a GET or HEAD endpoint must not change state, but this handler's effect is `writes`. Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.
⊢ (Handler.effect (DbState App) (Auth Me → Body NewMember → LeanApi.Tx App JoinError (Created MemberView))).Safe -/
#guard_msgs (error) in
example : DbEndpoint App := .get "/members" join

-- A `Tx` handler cannot hand back a `Current` row: the transaction index
-- is bound by `Tx` itself, so nothing outside can name it.
/-- error: Type mismatch
  Txn.get Member { toInt64 := 1 }
has type
  Txn ?m.3 ?m.4 ?m.5 (Option (Current ?m.3 Member))
but is expected to have type
  Txn σ✝ App Unit (Option (Current σ Member)) -/
#guard_msgs (error) in
example : Tx App Unit (Option (Current σ Member)) := Txn.get Member ⟨1⟩

/-- `DbApi.step` is the API's meaning; `gamesApi.step` reads as for `Api`. -/
example (env : Env) (r : Req) (st : DbState App) : api.step env r st = api.toApi.step env r st := rfl

-- `api!` checks path arity for database endpoints too.
/-- error: api!: GET /members/{a}/{b} has 2 path parameter(s), but `Tests.DbEndpoint.getMember` takes 1 `Path` argument(s):
  Auth Me → Path Nat → Read App (Except NotFound MemberView) -/
#guard_msgs (error) in
example : DbApi App := api! [.get "/members/{a}/{b}" getMember]

/-- The API's meaning is an ordinary typed API: the laws apply. -/
theorem api_step_safe (env : Env) (r : Req) (st : DbState App) (hm : r.method.Safe) :
    (api.toApi.step env r st).2 = st :=
  Api.step_safe _ env r st hm

/-- An invariant preserved by `join`'s transaction holds in every reachable
    state: reads carry no obligation. -/
theorem api_inductive (I : DbState App → Prop)
    (hjoin : ∀ (me : Auth Me) (b : Body NewMember) st, I st → I (Txn.denote (join me b (σ := Unit)) st).2)
    (hsignup : ∀ (b : Body Signup) st, I st → I (Txn.denote (signup b (σ := Unit)) st).2)
    (hdrop : ∀ (i : Nat) st, I st → I (Txn.denote (dropTeam ⟨i⟩ (σ := Unit)) st).2) :
    Props.Inductive (api.toApi.toSys I) I :=
  Api.inductive_of _ (fun _ h => h) (by
    intro e he
    simp only [DbApi.toApi, api, List.map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact fun _ _ => trivial
    · exact fun _ => trivial
    · exact fun _ => trivial
    · exact fun me b => hjoin me b
    · exact fun b => hsignup b
    · exact fun i => hdrop i)

/-- What a member may see: which session and member rows authenticate,
    and every member row of their team. -/
instance : ViewOf (DbState App) Me := ⟨fun me s₁ s₂ =>
  (∀ t, Read.denote (lookupSession t) s₁ = Read.denote (lookupSession t) s₂) ∧
  (∀ id, (Read.denote (Read.get Member id) s₁).filter (·.val.team == me.team) =
         (Read.denote (Read.get Member id) s₂).filter (·.val.team == me.team))⟩

def getMemberEp : DbEndpoint App := .get "/members/{id}" getMember

/-- **Isolation for `GET /members/{id}`**: for a request authenticated as
    `p`, the answer is the same in any two databases that look the same to
    `p`. Instantiates `Api.noninterference`. -/
theorem getMember_isolated (p : Me) (env : Env) (r : Req) {s₁ s₂ : DbState App}
    (hv : ViewOf.same p s₁ s₂) (ha : Authenticates.authenticate s₁ env r = .ok p) :
    (Api.step [getMemberEp.toEndpoint] env r s₁).1 = (Api.step [getMemberEp.toEndpoint] env r s₂).1 := by
  refine Api.noninterference _ p ?_ env r hv ha
  intro e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  subst he
  refine ⟨?_, ?_, fun who => ⟨trivial, fun a => ?_⟩⟩
  · -- authentication reads only what the view fixes
    intro env r s₁ s₂ ⟨hv, _⟩
    show Read.denote _ s₁ = Read.denote _ s₂
    simp only [AuthenticatesDb.authProg]
    split
    · rfl
    · have hb : ∀ (st : DbState App) (k : Option Me → Read App (Except AuthFailure Me)) t,
          Read.denote (lookupSession t >>= k) st = Read.denote (k (Read.denote (lookupSession t) st)) st :=
        fun _ _ _ => rfl
      rw [hb, hb, hv.1]
      split <;> rfl
  · intro env r s₁ s₂ a ⟨hv, ha⟩ ha'
    rw [ha] at ha'; cases ha'; exact hv
  · -- the body reads one member row, and answers only for a teammate
    intro env r s₁ s₂ ⟨_, _, hw⟩
    have h := hw ⟨Int64.ofNat a⟩
    have hb : ∀ (st : DbState App) (k : Option (Stored Member) → Read App (Except NotFound MemberView)),
        Read.denote (Read.get Member ⟨Int64.ofNat a⟩ >>= k) st =
          Read.denote (k (Read.denote (Read.get Member ⟨Int64.ofNat a⟩) st)) st := fun _ _ => rfl
    show ToResponse.toRes (Read.denote (getMember who ⟨a⟩) s₁) =
      ToResponse.toRes (Read.denote (getMember who ⟨a⟩) s₂)
    unfold getMember
    rw [hb, hb]
    revert h
    cases Read.denote (Read.get Member ⟨Int64.ofNat a⟩) s₁ <;>
      cases Read.denote (Read.get Member ⟨Int64.ofNat a⟩) s₂ <;>
      intro h <;> simp only [Option.filter] at h ⊢
    all_goals first
      | rfl
      | (split at h <;> first | cases h | (split at h <;> first | cases h | skip))
    all_goals (try (cases h)) <;> simp_all <;> rfl

/-! ## Runtime -/

private def freshPath (name : String) : IO System.FilePath := do
  let dir : System.FilePath := ".lake/test-db"
  IO.FS.createDirAll dir
  let path := dir / s!"{name}.sqlite"
  for ext in ["", "-wal", "-shm"] do
    let f : System.FilePath := path.toString ++ ext
    if ← f.pathExists then IO.FS.removeFile f
  return path

private def bearer (t : String) : String × String := ("Authorization", s!"Bearer {t}")

private def must (r : Except DbError α) (what : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw (IO.userError s!"{what}: {e}")

def run : TestM Unit := do
  section_ "LAPI-02: read programs served over SQLite" do
    let path ← freshPath "db-endpoint"
    let w ← must (← openDb path (IsSchema.specs App)) "seed conn"
    let (ada, grace, eve) ← must (← DbM.run w do
      let eng ← insert Team ⟨"eng"⟩
      let ops ← insert Team ⟨"ops"⟩
      let ada ← insert Member ⟨"ada", eng.id⟩
      let _ ← insert Member ⟨"alan", eng.id⟩
      let grace ← insert Member ⟨"grace", ops.id⟩
      let _ ← insert Session ⟨"tok-ada", ada.id⟩
      let _ ← insert Session ⟨"tok-grace", grace.id⟩
      return (ada, grace, eng)) "seed"
    let _ := eve
    let rd ← DbConns.open path (IsSchema.specs App) 2
    let logs ← IO.mkRef (#[] : Array String)
    let svc := api.service rd (log := fun l => logs.modify (·.push l))
    let r ← get svc s!"/members/{ada.id.toInt64.toInt}" [bearer "tok-ada"]
    checkEq "teammate 200" r.status 200
    checkEq "teammate body" (r.json?.bind fun j => (j.getObjValAs? String "name").toOption) (some "ada")
    let r ← get svc s!"/members/{grace.id.toInt64.toInt}" [bearer "tok-ada"]
    checkEq "other team 404" r.status 404
    checkEq "missing 404" (← get svc "/members/999" [bearer "tok-ada"]).status 404
    checkEq "no token 401" (← get svc "/members/1").status 401
    checkEq "bad token 401" (← get svc "/members/1" [bearer "nope"]).status 401
    checkEq "bad path 422" (← get svc "/members/x" [bearer "tok-ada"]).status 422
    let t ← get svc "/team" [bearer "tok-ada"]
    checkEq "team 200" t.status 200
    checkEq "team total" (t.json?.bind fun j => (j.getObjValAs? Nat "total").toOption) (some 2)
    let n ← get svc "/names?name=grace"
    checkEq "name taken" (n.json?.bind fun j => (j.getObjValAs? Bool "taken").toOption) (some true)
    checkEq "missing query 422" (← get svc "/names").status 422
    check "describe prints the Read signature"
      ((api.describe.splitOn "Read App (Except NotFound MemberView)").length > 1)

    -- The executed program agrees with the meaning over the loaded state.
    let st ← must (← DbM.run w (DbState.load (s := App))) "load"
    for (target, hs) in [(s!"/members/{ada.id.toInt64.toInt}", [bearer "tok-ada"]),
                         ("/team", [bearer "tok-grace"]), ("/names?name=zed", [])] do
      let req : Req := { method := .get, path := (target.splitOn "?").head!.splitOn "/" |>.filter (· != ""),
                         query := match (target.splitOn "?")[1]? with
                           | some q => q.splitOn "&" |>.map fun kv => match kv.splitOn "=" with
                               | [k, v] => (k, v) | _ => (kv, "")
                           | none => [],
                         headers := hs.map fun (k, v) => (k.toLower, v) }
      let env : Env := {}
      let got ← match Router.resolveIn api.toApi.entries .redirect req with
        | .route e ps => match api.find? (fun de => de.template == e.template && de.method == e.method) with
          | some de => DbProg.exec rd (de.prog env { req with params := ps })
          | none => pure (.ok {})
        | .respond res => pure (.ok res)
      match got with
      | .error f => check s!"{target}: fault {f}" false
      | .ok res =>
        let want := (api.toApi.step env req st).1
        checkEq s!"{target}: run = denote (load)" (res.status, String.fromUTF8! res.body) (want.status, String.fromUTF8! want.body)

    -- One snapshot per read: the count and the page of `/team` agree even
    -- when a writer commits in between (checked on the reader connection).
    let some reader := rd.readers[0]? | check "reader" false
    let observed ← DbM.run reader.conn (Read.run (s := App) (do
      let q := (Query.from Member (s := App)).where' (fun r => r.val.team == ada.val.team)
      let before ← Read.count q
      let page ← Read.page q { limit := some 10 }
      pure (before, page.total, page.items.length)))
    checkEq "count and page from one snapshot" (observed.toOption.bind (·.toOption)) (some (2, 2, 2))

    -- Authentication runs in the request's snapshot: a revoked token is
    -- refused by the next request.
    let _ ← must (← DbM.run w do
      match ← Read.exec (s := App) (Read.lookup Session Session.Unique.byToken "tok-grace") with
      | some s => delete s.id
      | none => pure ()) "revoke"
    checkEq "revoked token 401" (← get svc "/team" [bearer "tok-grace"]).status 401

    -- Transactions: commit, typed failure, abort discards writes.
    let jn := fun (tok nm : String) => request svc "POST" "/members"
      [bearer tok, ("Content-Type", "application/json")] (Json.mkObj [("name", .str nm)]).compress
    let r ← jn "tok-ada" "ann"
    checkEq "join 201" r.status 201
    check "join location" ((r.header? "location").isSome)
    checkEq "duplicate name 409" (← jn "tok-ada" "ann").status 409
    checkEq "bad body 422" (← request svc "POST" "/members"
      [bearer "tok-ada", ("Content-Type", "application/json")] "{}").status 422
    let r ← jn "tok-ada" "abe"
    checkEq "team full 409" r.status 409
    let gone ← get svc "/names?name=abe"
    checkEq "aborted insert discarded"
      (gone.json?.bind fun j => (j.getObjValAs? Bool "taken").toOption) (some false)
    checkEq "team still 3" ((← get svc "/team" [bearer "tok-ada"]).json?.bind
      fun j => (j.getObjValAs? Nat "total").toOption) (some 3)

    -- The write path agrees with the meaning: same answer, same next state.
    -- (grace's earlier token was revoked above; give her a new one.)
    let _ ← must (← DbM.run w (insert Session ⟨"tok-grace2", grace.id⟩)) "new session"
    let st0 ← must (← DbM.run w (DbState.load (s := App))) "load"
    let req : Req := { (default : Req) with
      method := Method.post, path := ["members"],
      headers := [("authorization", "Bearer tok-grace2"), ("content-type", "application/json")],
      body := (Json.mkObj [("name", .str "gus")]).compress.toUTF8 }
    let want := api.toApi.step {} req st0
    let got ← match Router.resolveIn api.toApi.entries .redirect req with
      | .route e ps => match api.find? (fun de => de.template == e.template && de.method == e.method) with
        | some de => DbProg.exec rd (de.prog {} { req with params := ps })
        | none => pure (.ok {})
      | .respond res => pure (.ok res)
    checkEq "write: run status = denote status" (got.toOption.map (·.status)) (some want.1.status)
    checkEq "write: committed" want.1.status 201
    let st1 ← must (← DbM.run w (DbState.load (s := App))) "reload"
    checkEq "write: member count matches the meaning's next state"
      (Read.denote (Read.count (Query.from Member (s := App))) st1)
      ((Read.denote (Read.count (Query.from Member (s := App))) st0) + 1)

    -- LAPI-03: LeanDB's failures answered by the defaults.
    let su := fun (nm : String) (team : Nat) => request svc "POST" "/signup"
      [("Content-Type", "application/json")] (Json.mkObj [("name", .str nm), ("team", Json.num team)]).compress
    let r ← su "ada" 1
    checkEq "duplicate → 409" r.status 409
    checkEq "no Location on a clash" (r.header? "location") none
    check "no holder id in the body" ((r.body.splitOn s!"{ada.id.toInt64.toInt}").length == 1)
    check "detail names the index" ((r.body.splitOn "name").length > 1)
    let r ← su "newbie" 999
    checkEq "missing team → 422" r.status 422
    check "missing ref names the field" ((r.body.splitOn "body.team").length > 1)
    checkEq "signup ok → 201" (← su "newbie" 1).status 201
    checkEq "delete referenced team → 409" (← request svc "DELETE" "/teams/1").status 409
    let r ← request svc "DELETE" "/teams/1"
    check "restricted does not say by what" ((r.body.splitOn "member").length == 1)
    checkEq "delete missing team → 404" (← request svc "DELETE" "/teams/999").status 404
    -- The opt-in wrapper names the referrer from the schema.
    match (ReferencedBy.all App Team)[0]? with
    | none => check "Team has an inbound key" false
    | some rb =>
      let body := (ToProblem.problem (ε := WithReferrers (DeleteError App Team)) ⟨.restricted
        (ReferencedBy.toRestricting rb rfl rfl) 2⟩).toJson.compress
      check s!"WithReferrers names table and column: {body}"
        ((body.splitOn "\"table\":\"member\"").length > 1 && (body.splitOn "\"column\":\"team\"").length > 1)
    let _ ← must (← DbM.run w (insert Team ⟨"empty"⟩)) "empty team"
    let empty := ((← must (← DbM.run w (Read.exec (s := App)
      (Read.all (Query.from Team (s := App))))) "teams").getLast?.map (·.id.toInt64.toInt)).getD 0
    checkEq "delete unreferenced team → 204" (← request svc "DELETE" s!"/teams/{empty}").status 204

    -- Two worlds that differ only in *who* holds the key answer the same.
    let other ← freshPath "db-endpoint-other"
    let w2 ← must (← openDb other (IsSchema.specs App)) "open other"
    let _ ← must (← DbM.run w2 do
      let t ← insert Team ⟨"x"⟩
      let _ ← insert Member ⟨"filler1", t.id⟩
      let _ ← insert Member ⟨"filler2", t.id⟩
      let _ ← insert Member ⟨"ada", t.id⟩
      pure ()) "seed other"
    let rd2 ← DbConns.open other (IsSchema.specs App) 1
    let svc2 := api.service rd2 (log := fun _ => pure ())
    let r1 ← su "ada" 1
    let r2 ← request svc2 "POST" "/signup" [("Content-Type", "application/json")]
      (Json.mkObj [("name", .str "ada"), ("team", Json.num 1)]).compress
    checkEq "clash bodies identical across holders" (r1.status, r1.body) (r2.status, r2.body)
    rd2.close

    -- Faults answer without effect, logged with the request id.
    let before ← must (← DbM.run w (DbState.load (s := App))) "before faults"
    let count := fun st => Read.denote (Read.count (Query.from Member (s := App))) st
    let lock ← must (← openDbRaw path) "locker"
    lock.raw.exec "PRAGMA busy_timeout = 0"
    lock.raw.exec "BEGIN IMMEDIATE"
    rd.writer.conn.raw.exec "PRAGMA busy_timeout = 0"
    let r ← jn "tok-ada" "zoe"
    checkEq "locked writer → 503" r.status 503
    checkEq "retry-after" (r.header? "retry-after") (some "1")
    check "no internal detail" ((r.body.splitOn "locked").length == 1)
    lock.raw.exec "ROLLBACK"
    rd.writer.conn.raw.exec "PRAGMA busy_timeout = 5000"
    let rdBad ← DbConns.open path (IsSchema.specs App) 1
    for c in rdBad.readers do c.conn.poison "test: connection lost"
    let svcBad := api.service rdBad (log := fun l => logs.modify (·.push l))
    let r ← get svcBad "/team" [bearer "tok-ada"]
    checkEq "poisoned reader → 500" r.status 500
    check "no internal detail (500)" ((r.body.splitOn "connection lost").length == 1)
    check "fault logged" ((← logs.get).any fun l => (l.splitOn "db_fault").length > 1)
    rdBad.close
    let after ← must (← DbM.run w (DbState.load (s := App))) "after faults"
    checkEq "faults wrote nothing" (count after) (count before)
    rd.close

/-! ## LAPI-03: the defaults ignore payloads; the wrappers do not -/

/-- With the defaults, the answer to a clash cannot depend on the holder:
    the isolation obligation never needs the holder in the caller's view. -/
example : ToProblem.Blind (InsertError.SameButHolder (α := Member)) := InsertError.blind_holder

instance : LocationOf Member := ⟨fun id => s!"/members/{id.toInt64.toInt}"⟩

-- With `WithHolder`, the same proof does not go through: it is stuck at the
-- payload, two different holders.
/-- error: Tactic `rfl` failed: The left-hand side
  ToProblem.problem { val := InsertError.duplicate ix✝ holder✝¹ }
is not definitionally equal to the right-hand side
  ToProblem.problem { val := InsertError.duplicate ix✝ holder✝ }

case duplicate.duplicate
holder✝¹ : LeanDb.Id Member
ix✝ : Unique Member
holder✝ : LeanDb.Id Member
⊢ ToProblem.problem { val := InsertError.duplicate ix✝ holder✝¹ } =
    ToProblem.problem { val := InsertError.duplicate ix✝ holder✝ } -/
#guard_msgs (error) in
example : ToProblem.Blind (fun e₁ e₂ : WithHolder (InsertError Member) =>
    InsertError.SameButHolder e₁.val e₂.val) := by
  intro ⟨e₁⟩ ⟨e₂⟩ h
  cases e₁ <;> cases e₂ <;> simp_all [InsertError.SameButHolder] <;> subst_vars <;> rfl

/-- And it is false outright: two holders at different places. -/
example : ¬ ToProblem.Blind (fun e₁ e₂ : WithHolder (InsertError Member) =>
    InsertError.SameButHolder e₁.val e₂.val) :=
  WithHolder.not_blind Member.Unique.byName ⟨1⟩ ⟨2⟩ (by decide)

end Tests.DbEndpoint
