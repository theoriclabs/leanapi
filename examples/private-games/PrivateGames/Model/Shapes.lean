/-
  private-games through the property library's other shapes (PLAN.md M12).

  * `movesGrow`: a stored game's move log only grows, and its revision
    never decreases (a step property, pulled back along the simulation to
    the store of games).
  * `reads_safe`: requests to the read routes are `Safe` in `gamesSys`
    (the library's statement of `reads_pure`), so they preserve every
    invariant with no further proof.
  * `gamesNI`: the per-caller isolation claim as an `NIPackage` over a
    projection, with its hiddenness witness and an `Enabled` companion.
  * `gamesKeyed_*`: the generic keyed idempotence theorem, instantiated for
    the list ledger that models the receipt table.
-/
import LeanApi.Props.Keyed
import PrivateGames.Model.Invariants
import PrivateGames.Model.Idempotence

namespace PrivateGames.Model

open LeanApi LeanApi.Props LeanApi.Proofs PrivateGames.App

/-! ## Monotonicity: move logs only grow -/

/-- `new` extends `old`: same id, moves extended, revision not lower. -/
def Extends (old new : Game) : Prop := old.moves <+: new.moves ∧ old.rev ≤ new.rev

instance (old new : Game) : Decidable (Extends old new) := by unfold Extends; infer_instance

theorem Extends.refl (g : Game) : Extends g g := ⟨List.prefix_refl _, Nat.le_refl _⟩

/-- The store of games, restricted to commands that extend the game. -/
def growStore : ListStore where
  Entity := Game
  Create := Game
  Cmd := Game
  Err := Unit
  id g := g.id.n
  create n g := if Valid g then .ok { g with id := ⟨n⟩ } else .error ()
  apply new old := if new.id = old.id ∧ Valid new ∧ Extends old new then .ok new else .error ()

/-- Every game of the earlier store is extended by the game with its id in
    the later store (games are never removed). -/
def StoreGrows (a b : growStore.World) : Prop :=
  ∀ g ∈ a.items, ∃ g' ∈ b.items, g'.id = g.id ∧ Extends g g'

theorem StoreGrows.refl (a : growStore.World) : StoreGrows a a := fun g hg => ⟨g, hg, rfl, Extends.refl g⟩

def toGrow (w : World) : growStore.World := { items := w.games, next := w.nextGame }

theorem toGrow_record (p : PlayerId) (k : Option Keyed) (res : Res) (w : World) :
    toGrow (recordReceipt p k res w) = toGrow w := by
  cases k <;> rfl

theorem growStore_grows : StepProp growStore.sys StoreGrows := by
  intro _ r w g hg
  cases r with
  | create c =>
    show ∃ g' ∈ (growStore.step (.create c) w).2.items, _
    simp only [ListStore.step]
    split
    · exact ⟨g, List.mem_append_left _ hg, rfl, Extends.refl g⟩
    · exact ⟨g, hg, rfl, Extends.refl g⟩
  | update t c =>
    show ∃ g' ∈ (growStore.step (.update t c) w).2.items, _
    simp only [ListStore.step]
    split
    · rename_i y hy
      simp only [growStore] at hy
      split at hy
      · rename_i hc; cases hy
        by_cases hgt : g = t
        · subst hgt
          refine ⟨c, ?_, hc.1, hc.2.2⟩
          exact List.mem_map.mpr ⟨g, hg, by simp; rfl⟩
        · refine ⟨g, ?_, rfl, Extends.refl g⟩
          exact List.mem_map.mpr ⟨g, hg, by simp [hgt]⟩
      · cases hy
    · exact ⟨g, hg, rfl, Extends.refl g⟩

/-- The domain facts: accepted moves and resignations extend the game. -/
theorem playMove_extends {p : PlayerId} {e : Revision} {c : Cell} {g g' : Game}
    (h : PrivateGames.playMove p e c g = .ok g') : Extends g g' := by
  obtain ⟨_, _, _, _, _, rfl⟩ := playMove_ok h
  exact ⟨⟨[c], rfl⟩, Nat.le_succ _⟩

theorem resign_extends {p : PlayerId} {g g' : Game} (h : PrivateGames.resign p g = .ok g') : Extends g g' := by
  obtain ⟨_, hc⟩ := resign_ok h
  rcases hc with ⟨_, rfl⟩ | ⟨_, _, rfl⟩
  · exact Extends.refl _
  · exact ⟨List.prefix_refl _, Nat.le_succ _⟩

def GrowOk : Write → Prop
  | .insertGame g => Valid g
  | .updateGame old new => new.id = old.id ∧ Extends old new

theorem decideCore_growOk {p : PlayerId} {i : Input} {s : Slice} {wr : Write} {b : Game → Res}
    (h : decideCore p i s = .write wr b) : GrowOk wr := by
  cases i with
  | readGame _ => simp only [decideCore] at h; split at h <;> cases h
  | listGames _ _ => simp only [decideCore] at h; cases h
  | openGame opp tc _ =>
    simp only [decideCore] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i g hg; cases h; exact openGame_valid hg
  | playMove _ rev cell _ =>
    simp only [decideCore] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i g _ g' hg; cases h; exact ⟨playMove_id hg, playMove_extends hg⟩
  | resign _ _ =>
    simp only [decideCore] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i g _ g' hg
        split at h
        · cases h
        · cases h; exact ⟨resign_id hg, resign_extends hg⟩

theorem core_growOk {p : PlayerId} {i : Input} {s : Slice} {wr : Write} {k : Option Keyed} {b : Game → Res}
    (h : core p i s = .write wr k b) : GrowOk wr := by
  simp only [core, withReceipt] at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h
    · rename_i wr' b' hd; cases h; exact decideCore_growOk hd

theorem commit_growSim (p : PlayerId) (wr : Write) (k : Option Keyed) (b : Game → Res) (w : World)
    (hw : GrowOk wr) :
    toGrow (commit p wr k b w).2 = toGrow w ∨
      ∃ r, toGrow (commit p wr k b w).2 = (growStore.step r (toGrow w)).2 := by
  cases wr with
  | insertGame g =>
    refine .inr ⟨.create g, ?_⟩
    have hv : Valid g := hw
    simp only [commit, toGrow_record]
    simp [toGrow, ListStore.step, growStore, hv] <;> rfl
  | updateGame old new =>
    simp only [commit]
    split
    · rename_i hok
      refine .inr ⟨.update old new, ?_⟩
      obtain ⟨hid, hext⟩ := hw
      simp only [commitOk, Bool.and_eq_true, beq_iff_eq] at hok
      have hv : Valid new := (Valid.holdsB_iff new).mp hok.1.1.2
      rw [toGrow_record]
      simp [toGrow, ListStore.step, growStore, hid, hv, hext, ListStore.replace]
      intro _ _; rfl
    · exact .inl rfl

theorem gamesSys_growSim : Simulation gamesSys growStore.sys toGrow where
  init w h := h
  step e r w := by
    show toGrow (gamesApp.step r w).2 = toGrow w ∨
      ∃ e' r', toGrow (gamesApp.step r w).2 = (growStore.step r' (toGrow w)).2
    simp only [ScopedApp.step]
    split
    · exact .inl rfl
    · simp only [ScopedApp.operate]
      split
      · exact .inl rfl
      · rename_i p _
        split
        · exact .inl rfl
        · rename_i i _
          change toGrow (runPlan p (core p i (load p w i.need)) w).2 = toGrow w ∨
            ∃ e' r', toGrow (runPlan p (core p i (load p w i.need)) w).2 = (growStore.step r' (toGrow w)).2
          cases hc : core p i (load p w i.need) with
          | respond _ => exact .inl rfl
          | write wr k b =>
            rcases commit_growSim p wr k b w (core_growOk hc) with h | ⟨r', h⟩
            · exact .inl h
            · exact .inr ⟨(), r', h⟩

/-- **Move logs only grow**, for every request: each game after a step
    extends the game with its id before the step (moves are a prefix,
    revision is not lower), and no game is removed. -/
theorem movesGrow : Monotone gamesSys toGrow StoreGrows :=
  StepProp.pullback gamesSys_growSim StoreGrows.refl growStore_grows

/-! ## Safe reads -/

/-- Requests routed to a read operation. -/
def IsRead (r : Req) : Prop :=
  ∃ op ps, Router.resolveIn entries .redirect r = .route op ps ∧ (op = .readGame ∨ op = .listGames)

/-- Respond plans are pure: the one fact about the plan type. -/
def gamesPure : ScopedApp.PurePlans gamesApp where
  pure p := ∃ res, p = .respond res
  run_pure _ p _ := by rintro ⟨res, rfl⟩; rfl

/-- **Reads are `Safe`**, discharged by the library from the plan type:
    `core` only plans responses for reads (`read_decide_respond`), and
    responses are pure. This replaces the hand proof of `reads_pure`. -/
theorem reads_safe : Safe gamesSys IsRead :=
  ScopedApp.safe_of_pure_plans gamesApp gamesInit gamesPure (fun op => op = .readGame ∨ op = .listGames)
    fun op a i s r hop hd => read_decide_respond a i s (decode_read op r i hop hd)

/-- So reads preserve every invariant with no per-invariant proof. -/
theorem reads_preserve (I : World → Prop) : ∀ e r w, IsRead r → I w → I (gamesSys.step e r w).2 :=
  Safe.preserves reads_safe I

/-! ## Noninterference package -/

/-- The caller's observation: the view is `SameView`'s data as a projection,
    and the observation is the complete response. -/
def gamesObs : Observation gamesSys where
  Observer := PlayerId
  View := List (String × PlayerId) × List Game × List (ReceiptKey × Receipt) × List PlayerId × Nat
  Obs := Res
  view p w := (w.sessions, visibleGames p w, ownReceipts p w, w.players, w.nextGame)
  obs _ r := r

theorem gamesObs_sameView {p : PlayerId} {w₁ w₂ : World} (h : gamesObs.SameView p w₁ w₂) :
    SameView p w₁ w₂ := by
  simp only [Observation.SameView, gamesObs, Prod.mk.injEq] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- A game between two other players. -/
def otherGame (p : PlayerId) : Game := Game.opened ⟨0⟩ ⟨p.n + 1⟩ ⟨p.n + 2⟩ TimeControl.default

theorem otherGame_hidden (p : PlayerId) : visible p (otherGame p) = false := by
  simp [visible, Game.isParticipant, otherGame, Game.opened]
  constructor <;> (intro h; have := congrArg PlayerId.n h; simp at this)

def emptyWorld : World := { games := [], sessions := [], players := [], receipts := [], nextGame := 1 }

theorem gamesObs_hidden : gamesObs.Hidden := by
  intro p
  refine ⟨emptyWorld, withHidden emptyWorld (otherGame p), ?_, ?_⟩
  · have h := withHidden_view (p := p) emptyWorld (otherGame p) (otherGame_hidden p)
    simp only [Observation.SameView, gamesObs, h.sessions, h.games, h.receipts, h.players, h.nextGame]
  · intro h
    have := congrArg World.games h
    simp [emptyWorld, withHidden] at this

/-- The enabledness companion's precondition: the request is routed to
    `GET /games/{id}`, authenticates as `p`, decodes, and the game is
    visible to `p`. -/
def ReadsOwn (w : World) (r : Req) : Prop :=
  ∃ p g gid ps, Router.resolveIn entries .redirect r = .route .readGame ps ∧
    authenticate { r with params := ps } w = .ok p ∧
    decode .readGame { r with params := ps } = .ok (.readGame gid) ∧
    (visibleGames p w).find? (·.id = gid) = some g

/-- **Availability over HTTP**: under `ReadsOwn`, the complete step answers
    with the game and status 200. -/
theorem reads_own_enabled : Enabled gamesSys ReadsOwn (fun res => res.status = 200) := by
  rintro _ w r ⟨p, g, gid, ps, hroute, hauth, hdec, hfind⟩
  show (gamesApp.step r w).1.status = 200
  have h1 : gamesApp.step r w = gamesApp.operate .readGame { r with params := ps } w := by
    simp [ScopedApp.step, gamesApp, hroute]
  rw [h1, ← gamesApp_step_route r w .readGame ps hroute]
  simp only [step, hroute, operate, hauth, hdec]
  rw [read_available p w g gid hfind]
  exact gameRes_status g

/-- **Isolation, as a library package.** Per-caller response
    noninterference over the projection `gamesObs`, a hiddenness witness
    (another player's game really is hidden, proved), and the `Enabled`
    companion `reads_own_enabled` (the response is not constant).

    The package takes the satisfiability of `ReadsOwn` as a hypothesis:
    exhibiting a concrete request needs the router and decoder to evaluate
    on string literals, which the kernel cannot do. It is **checked** by the
    HTTP tests ("participant reads their game → 200") and proved at the core
    level for every world by `read_available`. -/
def gamesNI (wit : ∃ w r, ReadsOwn w r) : NIPackage gamesSys gamesObs where
  acts p r w := gamesApp.AuthenticatesAs r w p
  ni p _ r _ _ hv ha := generic_isolation_caller r p (gamesObs_sameView hv) ha
  hidden := gamesObs_hidden
  enabledPre := ReadsOwn
  enabledOk res := res.status = 200
  enabled := reads_own_enabled
  enabledWitness := wit

end PrivateGames.Model

/-! ## Trace noninterference for a coalition of players (unwinding) -/

namespace PrivateGames.Model

open LeanApi LeanApi.Props LeanApi.Proofs PrivateGames.App

/-- Some member of `C` can see `g`. -/
def visibleC (C : List PlayerId) (g : Game) : Bool := C.any (visible · g)

/-- What the coalition `C` sees together. With `C = [p]` this is `p`'s view. -/
structure SameViewC (C : List PlayerId) (w₁ w₂ : World) : Prop where
  sessions : w₁.sessions = w₂.sessions
  games : w₁.games.filter (visibleC C) = w₂.games.filter (visibleC C)
  receipts : w₁.receipts.filter (fun x => C.contains x.1.actor) = w₂.receipts.filter (fun x => C.contains x.1.actor)
  players : w₁.players = w₂.players
  nextGame : w₁.nextGame = w₂.nextGame

theorem visibleC_of_mem {C : List PlayerId} {q : PlayerId} (hq : q ∈ C) {g : Game} (h : visible q g = true) :
    visibleC C g = true := List.any_eq_true.mpr ⟨q, hq, h⟩

/-- A member's view is part of the coalition's view. -/
theorem SameViewC.member {C : List PlayerId} {q : PlayerId} (hq : q ∈ C) {w₁ w₂ : World}
    (h : SameViewC C w₁ w₂) : SameView q w₁ w₂ := by
  refine ⟨h.sessions, ?_, ?_, h.players, h.nextGame⟩
  · have e : ∀ w : World, visibleGames q w = (w.games.filter (visibleC C)).filter (visible q) := by
      intro w
      simp only [visibleGames, List.filter_filter]
      congr 1; funext g
      cases hv : visible q g
      · simp
      · simp [visibleC_of_mem hq hv]
    rw [e, e, h.games]
  · have e : ∀ w : World, ownReceipts q w =
        (w.receipts.filter (fun x => C.contains x.1.actor)).filter (·.1.actor = q) := by
      intro w
      simp only [ownReceipts, List.filter_filter]
      congr 1; funext x
      by_cases hx : x.1.actor = q
      · simp [hx, hq]
      · simp [hx]
    rw [e, e, h.receipts]

theorem SameView.coalition {p : PlayerId} {w₁ w₂ : World} (h : SameView p w₁ w₂) : SameViewC [p] w₁ w₂ := by
  refine ⟨h.sessions, ?_, ?_, h.players, h.nextGame⟩
  · have hvc : visibleC [p] = visible p := by funext g; simp [visibleC]
    rw [hvc]; exact h.games
  · have := h.receipts; simpa [ownReceipts] using this

/-- Replacing `old` by `new` commutes with filtering by any predicate that
    agrees on them. -/
theorem filter_map_replace (f : Game → Bool) (old new : Game) (gs : List Game) (hf : f old = f new) :
    (gs.map fun g => if g = old then new else g).filter f =
      (gs.filter f).map (fun g => if g = old then new else g) := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    by_cases hg : g = old
    · subst hg; simp [List.filter_cons, hf, ih]; split <;> simp_all
    · simp [List.filter_cons, hg, ih]; split <;> simp_all

theorem recordReceipt_viewC {C : List PlayerId} {p : PlayerId} {k : Option Keyed} {res : Res} {w₁ w₂ : World}
    (h : SameViewC C w₁ w₂) : SameViewC C (recordReceipt p k res w₁) (recordReceipt p k res w₂) := by
  obtain ⟨a1, b1, c1, d1⟩ := record_fields p k res w₁
  obtain ⟨a2, b2, c2, d2⟩ := record_fields p k res w₂
  refine ⟨by rw [a1, a2]; exact h.sessions, by rw [d1, d2]; exact h.games, ?_, by rw [b1, b2]; exact h.players,
    by rw [c1, c2]; exact h.nextGame⟩
  cases k with
  | none => exact h.receipts
  | some k => simp only [recordReceipt, List.filter_append, h.receipts]

/-- A commit by a coalition member preserves the coalition's view. -/
theorem commit_viewC {C : List PlayerId} {q : PlayerId} (hq : q ∈ C) (wr : Write) (k : Option Keyed)
    (b : Game → Res) {w₁ w₂ : World} (h : SameViewC C w₁ w₂) :
    SameViewC C (commit q wr k b w₁).2 (commit q wr k b w₂).2 := by
  cases wr with
  | insertGame g =>
    simp only [commit, h.nextGame]
    refine recordReceipt_viewC ⟨h.sessions, ?_, h.receipts, h.players, rfl⟩
    simp only [List.filter_append, h.games]
  | updateGame old new =>
    simp only [commit, commitOk_view (h.member hq)]
    split
    · rename_i hok
      refine recordReceipt_viewC ⟨h.sessions, ?_, h.receipts, h.players, h.nextGame⟩
      simp only [commitOk, Bool.and_eq_true, beq_iff_eq] at hok
      obtain ⟨⟨⟨_, _⟩, hx⟩, ho⟩ := hok
      have hf : visibleC C old = visibleC C new := by
        simp only [visibleC]; congr 1; funext q'; exact visible_eq_of_participants hx ho
      show (w₁.games.map _).filter (visibleC C) = (w₂.games.map _).filter (visibleC C)
      rw [filter_map_replace _ old new _ hf, filter_map_replace _ old new _ hf, h.games]
    · exact h

/-- Under session table `sess`, the request authenticates as a member of
    `C` or as no one. Scoped to the session table (which no proved route
    changes, `step_sessions`), not to every conceivable world: otherwise
    some world would map the token to an outsider and the premise would be
    unsatisfiable for every authenticated request. -/
def ByCoalition (C : List PlayerId) (sess : List (String × PlayerId)) (r : Req) : Prop :=
  ∀ w op ps q, w.sessions = sess → Router.resolveIn entries .redirect r = .route op ps →
    authenticate { r with params := ps } w = .ok q → q ∈ C

theorem authenticate_params (r : Req) (ps : List (String × String)) (w : World) :
    authenticate { r with params := ps } w = authenticate r w := by
  simp [authenticate, authDigest, Req.header?, bearerToken?]

/-- `ByCoalition` is satisfiable: a request that authenticates as a member
    is by the coalition. -/
theorem byCoalition_of_auth {C : List PlayerId} {r : Req} {w : World} {p : PlayerId}
    (ha : authenticate r w = .ok p) (hp : p ∈ C) : ByCoalition C w.sessions r := by
  intro w' op ps q hs _ hq
  rw [authenticate_params, authenticate_view hs, ha] at hq
  cases hq; exact hp

/-- No proved route changes the session table. -/
theorem step_sessions (r : Req) (w : World) : (step r w).2.sessions = w.sessions := by
  unfold step
  cases Router.resolveIn entries .redirect r with
  | respond _ => rfl
  | route op ps =>
    simp only [operate]
    cases authenticate { r with params := ps } w with
    | error _ => rfl
    | ok q =>
      simp only
      cases decode op { r with params := ps } with
      | error _ => rfl
      | ok i =>
        simp only
        cases core q i (load q w i.need) with
        | respond _ => rfl
        | write wr k b =>
          cases wr with
          | insertGame g => simp only [runPlan, commit]; exact (record_fields _ _ _ _).1
          | updateGame old new =>
            simp only [runPlan, commit]; split
            · exact (record_fields _ _ _ _).1
            · rfl

/-- **Unwinding for a coalition.** Any request by a member of `C` (or by
    no one) preserves the coalition's view relation. -/
theorem step_viewC {C : List PlayerId} {r : Req} {w₁ w₂ : World} (hr : ByCoalition C w₁.sessions r)
    (h : SameViewC C w₁ w₂) : SameViewC C (step r w₁).2 (step r w₂).2 := by
  unfold step
  cases hroute : Router.resolveIn entries .redirect r with
  | respond _ => exact h
  | route op ps =>
    simp only [operate]
    rw [authenticate_view h.sessions]
    cases hauth : authenticate { r with params := ps } w₂ with
    | error _ => exact h
    | ok q =>
      have hq := hr w₂ op ps q h.sessions.symm hroute hauth
      simp only
      cases decode op { r with params := ps } with
      | error _ => exact h
      | ok i =>
        simp only
        rw [load_view (h.member hq)]
        cases core q i (load q w₂ i.need) with
        | respond _ => exact h
        | write wr k b => exact commit_viewC hq wr k b h

/-- **Successor view for one caller** (an EVIDENCE open item): a request
    that authenticates as `p` preserves `p`'s view, even when other
    players' views differ. -/
theorem step_view_caller {p : PlayerId} {r : Req} {w₁ w₂ : World} (ha : authenticate r w₁ = .ok p)
    (h : SameView p w₁ w₂) : SameView p (step r w₁).2 (step r w₂).2 :=
  (step_viewC (byCoalition_of_auth ha (List.mem_singleton_self p)) h.coalition).member
    (List.mem_singleton_self p)

def runReqs : List Req → World → World
  | [], w => w
  | r :: rs, w => runReqs rs (step r w).2

theorem runReqs_viewC {C : List PlayerId} (sess : List (String × PlayerId)) (rs : List Req)
    (hrs : ∀ r ∈ rs, ByCoalition C sess r) {w₁ w₂ : World} (hs : w₁.sessions = sess)
    (h : SameViewC C w₁ w₂) : SameViewC C (runReqs rs w₁) (runReqs rs w₂) := by
  induction rs generalizing w₁ w₂ with
  | nil => exact h
  | cons r rs ih =>
    exact ih (fun r' h' => hrs r' (List.mem_cons_of_mem _ h')) (by rw [step_sessions]; exact hs)
      (step_viewC (hs ▸ hrs r List.mem_cons_self) h)

/-- **Trace noninterference for several actors.** Two worlds that agree on
    everything a coalition `C` can see, run through the same sequence of
    requests from members of `C` (interleaved in any order): every member's
    response at the end is the same in both. Games no member participates
    in, and other players' receipts, may differ arbitrarily and are never
    revealed, however many requests the coalition sends. Requests by
    players outside `C` are excluded: they can legitimately change what `C`
    sees (an outsider opens a game with a member). -/
theorem trace_noninterference {C : List PlayerId} (rs : List Req) {w₁ w₂ : World}
    (hrs : ∀ r ∈ rs, ByCoalition C w₁.sessions r)
    {p : PlayerId} (hp : p ∈ C) (r : Req) (h : SameViewC C w₁ w₂)
    (ha : gamesApp.AuthenticatesAs r (runReqs rs w₁) p) :
    (step r (runReqs rs w₁)).1 = (step r (runReqs rs w₂)).1 := by
  have hv := (runReqs_viewC w₁.sessions rs hrs rfl h).member hp
  have := generic_isolation_caller r p hv ha
  have e : ∀ w : World, (gamesApp.step r w).1 = (Model.step r w).1 := by
    intro w
    cases hroute : Router.resolveIn entries .redirect r with
    | respond _ => simp [ScopedApp.step, Model.step, hroute, gamesApp]
    | route op ps =>
      rw [gamesApp_step_route r w op ps hroute]; simp [ScopedApp.step, gamesApp, hroute]
  exact (e (runReqs rs w₁)).symm.trans (this.trans (e (runReqs rs w₂)))

end PrivateGames.Model

/-! ## Keyed idempotence through the generic transformer -/

namespace PrivateGames.Model

open LeanApi LeanApi.Props PrivateGames.App

/-- The key's scope, computed by the library from the request (not chosen
    by the app): the bearer token's digest and the route. Two requests share
    a scope only if they carry the same credential and hit the same route,
    so a receipt is never replayed to another caller. Requests that do not
    route or carry no well-formed credential get the scope `none`. -/
def reqScope (r : gamesSys.Req) : Option (String × Op) :=
  match Router.resolveIn entries .redirect r, authDigest r with
  | .route op _, .ok d => some (d, op)
  | _, _ => none

/-- The fingerprint: the canonical decoded input (its retry identity). -/
def reqFp (r : gamesSys.Req) : Option String :=
  match Router.resolveIn entries .redirect r with
  | .respond _ => none
  | .route op ps => match decode op { r with params := ps } with
    | .ok i => (i.keyed.map (·.fingerprint)) <|> some op.name
    | .error _ => none

abbrev gamesLedger := listLedger (Option (String × Op) × String) (Option String × gamesSys.Res)

def gamesKeyed : Sys := Keyed gamesSys reqScope reqFp gamesLedger

/-- **Keyed idempotence for private-games, after any interleaving**: the
    library theorem, instantiated. The first keyed request with a fresh key
    runs the service; after any sequence of requests from anyone, the same
    keyed request replays the first response and changes nothing. -/
theorem gamesKeyed_replay_after (r : gamesSys.Req) (key : String) (w : gamesKeyed.World)
    (h : gamesLedger.lookup w.2 (reqScope r, key) = none)
    (between : List (Unit × gamesKeyed.Req)) :
    let first := gamesKeyed.step () (r, some key) w
    let wn := Keyed.run _ between first.2
    gamesKeyed.step () (r, some key) wn = (.replay (gamesSys.step () r w.1).1, wn) :=
  Keyed.keyed_replay_after (listLedger_laws _ _) r key () () w h between

/-- Reusing a key with a different input is refused (and changes nothing):
    the EVIDENCE item that was only checked natively, proved for the keyed
    model. -/
theorem gamesKeyed_reuse (r : gamesSys.Req) (key : String) (w : gamesKeyed.World) (f : Option String)
    (res : gamesSys.Res) (h : gamesLedger.lookup w.2 (reqScope r, key) = some (f, res)) (hf : f ≠ reqFp r) :
    gamesKeyed.step () (r, some key) w = (.keyReused, w) :=
  Keyed.keyed_reuse r key () w f res h hf

end PrivateGames.Model

/-! ## Keyed replay after any interleaving, for the model's own receipts -/

namespace PrivateGames.Model

open LeanApi LeanApi.Props PrivateGames.App

/-- No proved route removes or changes a receipt: receipts only grow. -/
theorem step_receipts (r : Req) (w : World) : ∃ xs, (step r w).2.receipts = w.receipts ++ xs := by
  have hrec : ∀ (p : PlayerId) (k : Option Keyed) (res : Res) (w : World),
      ∃ xs, (recordReceipt p k res w).receipts = w.receipts ++ xs := by
    intro p k res w; cases k with
    | none => exact ⟨[], by simp [recordReceipt]⟩
    | some k => exact ⟨_, rfl⟩
  unfold step
  cases Router.resolveIn entries .redirect r with
  | respond _ => exact ⟨[], by simp⟩
  | route op ps =>
    simp only [operate]
    cases authenticate { r with params := ps } w with
    | error _ => exact ⟨[], by simp⟩
    | ok q =>
      simp only
      cases decode op { r with params := ps } with
      | error _ => exact ⟨[], by simp⟩
      | ok i =>
        simp only
        cases core q i (load q w i.need) with
        | respond _ => exact ⟨[], by simp [runPlan]⟩
        | write wr k b =>
          cases wr with
          | insertGame g => simp only [runPlan, commit]; exact hrec _ _ _ _
          | updateGame old new =>
            simp only [runPlan, commit]; split
            · exact hrec _ _ _ _
            · exact ⟨[], by simp⟩

theorem runReqs_receipts (rs : List Req) (w : World) :
    ∃ xs, (runReqs rs w).receipts = w.receipts ++ xs ∧ (runReqs rs w).sessions = w.sessions := by
  induction rs generalizing w with
  | nil => exact ⟨[], by simp [runReqs], rfl⟩
  | cons r rs ih =>
    obtain ⟨xs, h1, h2⟩ := ih (step r w).2
    obtain ⟨ys, h3⟩ := step_receipts r w
    refine ⟨ys ++ xs, ?_, ?_⟩
    · show (runReqs rs (step r w).2).receipts = _; rw [h1, h3, List.append_assoc]
    · show (runReqs rs (step r w).2).sessions = _; rw [h2, step_sessions]

/-- A receipt found by the scoped load stays the first match after any
    later requests. -/
theorem find_receipt_stable (p : PlayerId) (k : Keyed) (w : World) (rs : List Req) (e : ReceiptKey × Receipt)
    (h : (ownReceipts p w).find? (fun (x : ReceiptKey × Receipt) => x.1.op = k.op ∧ x.1.key = k.key) = some e) :
    (ownReceipts p (runReqs rs w)).find? (fun (x : ReceiptKey × Receipt) => x.1.op = k.op ∧ x.1.key = k.key) = some e := by
  obtain ⟨xs, hx, _⟩ := runReqs_receipts rs w
  simp only [ownReceipts] at h ⊢
  rw [hx, List.filter_append, List.find?_append, h]; rfl

/-- **Keyed idempotence after any interleaving, for the model itself.**
    Like `keyed_replay`, but any sequence of requests (from any player,
    keyed or not) may run between the committed keyed request and its
    replay. The replay returns the recorded response, marked, and changes
    nothing. This is the model's own receipt path, not the `Keyed`
    wrapper. -/
theorem keyed_replay_after (r : Req) (w : World) (p : PlayerId) (op : Op) (ps : List (String × String))
    (i : Input) (k : Keyed) (wr : Write) (build : Game → Res)
    (hroute : Router.resolveIn entries .redirect r = .route op ps)
    (hauth : authenticate { r with params := ps } w = .ok p)
    (hdec : decode op { r with params := ps } = .ok i)
    (hk : i.keyed = some k)
    (hfresh : Fresh p k w)
    (hplan : core p i (load p w i.need) = .write wr (some k) build)
    (hcommitted : (commit p wr (some k) build w).1 ≠ hidden ∨ ∃ g, wr = .insertGame g)
    (rs : List Req) :
    step r (runReqs rs (step r w).2) = (markReplay (step r w).1, runReqs rs (step r w).2) := by
  have hfirst : step r w = commit p wr (some k) build w := by
    rw [resolve_route_params hroute]; simp only [operate, hauth, hdec, hplan, runPlan]
  rw [hfirst]
  generalize hwn : runReqs rs (commit p wr (some k) build w).2 = wn
  obtain ⟨_, _, hs⟩ := runReqs_receipts rs (commit p wr (some k) build w).2
  rw [hwn] at hs
  have hs0 : (commit p wr (some k) build w).2.sessions = w.sessions := by
    cases wr with
    | insertGame g => simp [commit, (record_fields _ _ _ _).1]
    | updateGame old new =>
      simp only [commit]; split
      · exact (record_fields _ _ _ _).1
      · rfl
  have hauth' : authenticate { r with params := ps } wn = .ok p := by
    rw [authenticate_view (hs.trans hs0), hauth]
  have hfind := find_receipt_stable p k _ rs _ (commit_records p wr k build w hfresh hcommitted)
  rw [hwn] at hfind
  have hrc := load_receipt p wn i k _ hk hfind
  rw [resolve_route_params hroute]
  simp only [operate, hauth', hdec]
  rw [core_replay p i _ k _ hk hrc rfl]
  simp [runPlan, Receipt.toRes, Receipt.ofRes]

end PrivateGames.Model
