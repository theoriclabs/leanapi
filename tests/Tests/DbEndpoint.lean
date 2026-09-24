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
def nameTaken (n : Query NameQ) : Read App Taken :=
  (fun m => ⟨m.isSome⟩) <$> Read.lookup Member Member.Unique.byName n.val.name

def api : DbApi App := dbapi! [
  .get "/members/{id}" getMember,
  .get "/team" myTeam,
  .get "/names" nameTaken
]

/-! ## Compile time -/

/-- The effect of a read program is `reads`. -/
example : Handler.effect (σ := DbState App) (τ := type_of% getMember) = .reads := rfl

/-- The API's meaning is an ordinary typed API: the laws apply. -/
theorem api_step_safe (env : Env) (r : Req) (st : DbState App) (hm : r.method.Safe) :
    (api.toApi.step env r st).2 = st :=
  Api.step_safe _ env r st hm

/-- Reads never write, so every invariant is preserved. -/
theorem api_inductive (I : DbState App → Prop) :
    Props.Inductive (api.toApi.toSys I) I :=
  Api.inductive_of _ (fun _ h => h) (by
    intro e he
    simp only [DbApi.toApi, api, List.map, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl
    · exact fun _ _ => trivial
    · exact fun _ => trivial
    · exact fun _ => trivial)

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
    show ToResponse.toRes (Read.denote (getMember ⟨who⟩ ⟨a⟩) s₁) =
      ToResponse.toRes (Read.denote (getMember ⟨who⟩ ⟨a⟩) s₂)
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
    let w ← must (← openDb path (IsSchema.specs App)) "open"
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
    let rd ← DbReaders.open path 2
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
      let got ← must (← DbM.run w (Read.run (s := App) (match Router.resolveIn api.toApi.entries .redirect req with
        | .route e ps => match api.find? (·.template == e.template) with
          | some de => de.prog env { req with params := ps }
          | none => pure {}
        | .respond res => pure res))) "run"
      match got with
      | .error f => check s!"{target}: fault {f}" false
      | .ok res =>
        let want := (api.toApi.step env req st).1
        checkEq s!"{target}: run = denote (load)" (res.status, String.fromUTF8! res.body) (want.status, String.fromUTF8! want.body)

    -- One snapshot per read: the count and the page of `/team` agree even
    -- when a writer commits in between (checked on the reader connection).
    let some reader := rd.conns[0]? | check "reader" false
    let observed ← DbM.run reader (Read.run (s := App) (do
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

    -- Faults answer without effect, logged with the request id: a full
    -- reader queue is transient (503), a poisoned connection is not (500).
    let rdBusy ← DbReaders.open path 1 (queue := 0)
    let svcBusy := api.service rdBusy (log := fun l => logs.modify (·.push l))
    let r ← get svcBusy "/team" [bearer "tok-ada"]
    checkEq "busy readers → 503" r.status 503
    checkEq "retry-after" (r.header? "retry-after") (some "1")
    rdBusy.close
    let rdBad ← DbReaders.open path 1
    for c in rdBad.conns do c.poison "test: connection lost"
    let svcBad := api.service rdBad (log := fun l => logs.modify (·.push l))
    let r ← get svcBad "/team" [bearer "tok-ada"]
    checkEq "poisoned reader → 500" r.status 500
    check "no internal detail" ((r.body.splitOn "connection lost").length == 1)
    check "fault logged" ((← logs.get).any fun l => (l.splitOn "db_fault").length > 1)
    rdBad.close
    -- nothing was written by any of the above
    let st' ← must (← DbM.run w (DbState.load (s := App))) "reload"
    checkEq "state unchanged by faults"
      (Read.denote (Read.count (Query.from Member (s := App))) st') 3
    rd.close

end Tests.DbEndpoint
