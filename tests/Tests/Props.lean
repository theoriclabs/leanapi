/-
  Check-before-proving regressions (PLAN.md M10) and authoring checks (M9).

  The two M10 regression targets must be found automatically:

  1. "unique ids without `Fresh`": `#check_invariant` on the store of games
     reports a counterexample to induction whose world is not reachable,
     and says `I ∧ pre I` is the next candidate.
  2. Review C1-style vacuity: an observation whose view determines the world
     fails the hiddenness-witness check, while private-games' `SameView`
     passes it.
-/
import LeanApi
import PrivateGames.Model.Invariants

namespace Tests.Props

open LeanApi LeanApi.Test LeanApi.Props PrivateGames PrivateGames.Model

deriving instance Enumerate for PlayerId, GameId, Cell, TimeControl, Game

/-! ## The store of games: small worlds -/

def g0 : Game := Game.opened ⟨0⟩ ⟨1⟩ ⟨2⟩ TimeControl.default
def g1 : Game := Game.opened ⟨1⟩ ⟨1⟩ ⟨2⟩ TimeControl.default

def storeWorlds : List gameStore.World :=
  let games := [[], [g0], [g1], [g0, g1], [g0, g0]]
  games.flatMap fun gs => (List.range 3).map fun n => { items := gs, next := n }

instance uniqueDec : DecidablePred (α := gameStore.sys.World) gameStore.UniqueIds :=
  fun w => by unfold ListStore.UniqueIds; infer_instance
instance freshDec : DecidablePred (α := gameStore.sys.World) gameStore.Fresh :=
  fun w => by unfold ListStore.Fresh; infer_instance

def showStore (w : gameStore.World) : String :=
  s!"⟨ids {w.items.map (·.id.n)}, next {w.next}⟩"

def storeSpec : CheckSpec gameStore.sys where
  worlds := storeWorlds
  envs := [()]
  reqs := [.create (⟨1⟩, ⟨2⟩, TimeControl.default)]
  initB w := w.items.isEmpty
  beq a b := a.items == b.items && a.next == b.next
  showW := showStore
  showR _ := "create"
  depth := 3

def uniqueReport := checkInvariant gameStore.sys storeSpec "UniqueIds" gameStore.UniqueIds

def freshUnique (w : gameStore.sys.World) : Prop := gameStore.Fresh w ∧ gameStore.UniqueIds w
instance : DecidablePred freshUnique := fun w => by
  unfold freshUnique; exact @instDecidableAnd _ _ (freshDec w) (uniqueDec w)

def freshReport := checkInvariant gameStore.sys storeSpec "Fresh ∧ UniqueIds" freshUnique

/-! ## Vacuity -/

def trueReport := checkInvariant gameStore.sys storeSpec "True" (fun _ => True)
def falseReport := checkInvariant gameStore.sys storeSpec "False" (fun _ => False)

/-- Review H3 (eb67460): initial worlds 0 and 1, invariant `n % 2 = 0`.
    Initial world 1 violates it, and the step preserves parity, so there is
    no CTI: the checker must still not call it inductive. -/
abbrev parity01 : Sys :=
  { World := Nat, Req := Unit, Res := Unit, Env := Unit,
    step := fun _ _ n => ((), n + 2), init := fun n => n = 0 ∨ n = 1 }

def parity01Spec : CheckSpec parity01 :=
  { worlds := List.range 10, envs := [()], reqs := [()], initB := fun n => n == 0 || n == 1,
    beq := (· == ·), showW := toString, showR := fun _ => "tick" }

def parityReport := checkInvariant parity01 parity01Spec "even" (fun n => n % 2 = 0)

/-! ## Hiddenness witnesses (review C1) -/

/-- Small model worlds: games among players 1, 2, 3. -/
def gA : Game := Game.opened ⟨1⟩ ⟨1⟩ ⟨2⟩ TimeControl.default
def gB : Game := Game.opened ⟨2⟩ ⟨2⟩ ⟨3⟩ TimeControl.default

def modelWorlds : List World :=
  [[], [gA], [gB], [gA, gB]].map fun gs =>
    { games := gs, sessions := [], players := [⟨1⟩, ⟨2⟩, ⟨3⟩], receipts := [], nextGame := 3 }

def modelEq (a b : World) : Bool := a.games == b.games && a.nextGame == b.nextGame

/-- private-games' caller view, as data. -/
def callerView (p : PlayerId) (w : World) : List Game × Nat := (visibleGames p w, w.nextGame)

/-- C1: the all-players view. It determines every game (each game is
    visible to its players), so it has no hiddenness witness. -/
def allView (_ : PlayerId) (w : World) : List (List Game) := [⟨1⟩, ⟨2⟩, ⟨3⟩].map fun q => visibleGames q w

def showModel (w : World) : String := s!"games {w.games.map (·.id.n)}"

def callerHidden := checkHidden modelWorlds modelEq [⟨1⟩, ⟨3⟩] callerView (toString ·.n) showModel
def allHidden := checkHidden modelWorlds modelEq [⟨1⟩, ⟨3⟩] allView (toString ·.n) showModel

/-! ## Isolation package (review H2, eb67460) -/

/-- No package can cover no requests (`acts := False`)… -/
example (P : NIPackage gamesSys gamesObs) (a : gamesObs.Observer) (h : ∀ r w, ¬ P.acts a r w) : False :=
  let ⟨_, _, ha⟩ := P.acts_nonempty a
  h _ _ ha

/-- …or call every response a success (`ok := True`). -/
example (P : NIPackage gamesSys gamesObs) (h : ∀ a o, P.ok a o) : False :=
  let ⟨a, o, hn⟩ := P.ok_nontrivial
  hn (h a o)

/-- A concrete request for `ReadPlumbing`, the one assumption of `gamesNI`. -/
def plumbingReq : Req :=
  { method := .get, path := ["games", "1"], headers := [("authorization", "Bearer tok")] }

/-- `ReadPlumbing`, evaluated on `plumbingReq`. -/
def plumbingHolds : Bool :=
  match Router.resolveIn PrivateGames.App.entries .redirect plumbingReq with
  | .route .readGame ps =>
    (match PrivateGames.App.decode .readGame { plumbingReq with params := ps } with
      | .ok (.readGame _) => true
      | _ => false) &&
    (match PrivateGames.App.authDigest plumbingReq with
      | .ok _ => true
      | .error _ => false)
  | _ => false

/-! ## Authoring -/

def badGame : Game := { g0 with rev := 5, x := ⟨2⟩ }

def run : TestM Unit := do
  section_ "check before proving: unique ids without Fresh (M10)" do
    let r := uniqueReport
    IO.println (r.render.splitOn "\n" |>.map ("    " ++ ·) |> "\n".intercalate)
    check "CTI found for UniqueIds" (!r.ctis.isEmpty)
    check "CTI world is not reachable (strengthen, not false)" (r.ctis.all (·.reachableAt.isNone))
    check "CTI world has next equal to an existing id" (r.ctis.any fun c => c.world == "⟨ids [0], next 0⟩")
    check "not vacuous" (!r.vacuous)
    let f := freshReport
    check "Fresh ∧ UniqueIds has no CTI" f.ctis.isEmpty
  section_ "check before proving: vacuity" do
    check "True is reported vacuous (rules nothing out)" (trueReport.violating.isNone && trueReport.vacuous)
    check "False is reported vacuous (no initial world)" (falseReport.initWitness.isNone && falseReport.vacuous)
  section_ "isolation package: its one assumption (review H2)" do
    check "private-games: read plumbing (ReadPlumbing holds for GET /games/1 with a bearer token)" plumbingHolds
  section_ "check before proving: every initial world (review H3)" do
    checkEq "the violating initial world is reported" parityReport.initViolations ["1"]
    check "no CTI among the searched steps" parityReport.ctis.isEmpty
    check "never reported inductive" ((parityReport.render.splitOn "✓ inductive").length == 1)
  section_ "check before proving: hiddenness witness (review C1)" do
    IO.println (renderHidden allHidden)
    check "caller view has a hiddenness witness for every observer" (callerHidden.all (·.witness.isSome))
    check "all-players view fails the witness check" (allHidden.all (·.witness.isNone))
  section_ "invariant: generated runtime check (M9)" do
    checkEq "valid game passes" (Valid.check g0 |>.toOption) (some ())
    match Valid.check badGame with
    | .error fs => checkEq "failing fields are named" fs ["distinct", "rev"]
    | .ok () => check "bad game fails" false
    checkEq "holdsB agrees" (Valid.holdsB badGame) false
    match Valid.stored.guardLoad "stored game 0" badGame with
    | .error msg => check "storage error names the fields" (msg.contains "failing: distinct, rev")
    | .ok _ => check "guardLoad refuses" false

end Tests.Props
