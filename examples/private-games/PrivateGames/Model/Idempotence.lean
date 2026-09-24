/-
  Idempotence (decision 0010) and the other M6 theorems.

  * `keyed_replay`: replaying a keyed request that was committed returns the
    recorded response, marked as a replay, and leaves the world unchanged.
  * `reads_pure`: requests to GET routes never change the world.
  * `resign_state_idem`: a second unkeyed resignation changes nothing.
  * `read_available`: a participant's read of their game succeeds.
-/
import PrivateGames.Model.Existence

namespace PrivateGames.Model

open LeanApi PrivateGames.App

/-! ## Retry handling in `core` -/

theorem core_replay (p : PlayerId) (i : Input) (s : Slice) (k : Keyed) (rc : Receipt)
    (hk : i.keyed = some k) (hs : s.receipt = some rc) (hf : rc.fingerprint = k.fingerprint) :
    core p i s = .respond rc.toRes := by
  simp [core, withReceipt, hk, hs, hf]

theorem need_receipt (i : Input) (k : Keyed) (hk : i.keyed = some k) :
    i.need.receipt = some (k.op, k.key) := by
  cases i <;> simp_all [Input.need]

/-- If the world holds a receipt for `(p, op, key)`, the scoped load finds it
    (the first one; `recordReceipt` only ever adds a key once, see below). -/
theorem load_receipt (p : PlayerId) (w : World) (i : Input) (k : Keyed) (rc : Receipt)
    (hk : i.keyed = some k)
    (hfind : (ownReceipts p w).find? (fun (x : ReceiptKey × Receipt) => x.1.op = k.op ∧ x.1.key = k.key) =
      some (⟨p, k.op, k.key⟩, rc)) :
    (load p w i.need).receipt = some rc := by
  simp only [load, need_receipt i k hk, Option.bind_some, hfind, Option.map_some]

/-! ## The replay theorem -/

/-- An actor's receipts contain no entry for this key yet. -/
def Fresh (p : PlayerId) (k : Keyed) (w : World) : Prop :=
  ∀ x ∈ ownReceipts p w, ¬ (x.1.op = k.op ∧ x.1.key = k.key)

theorem find_after_fresh {p : PlayerId} {k : Keyed} {w : World} {e : ReceiptKey × Receipt}
    (hf : Fresh p k w) (he : e.1.op = k.op ∧ e.1.key = k.key) :
    (ownReceipts p w ++ [e]).find? (fun (x : ReceiptKey × Receipt) => x.1.op = k.op ∧ x.1.key = k.key) = some e := by
  rw [List.find?_append]
  have : (ownReceipts p w).find? (fun (x : ReceiptKey × Receipt) => Decidable.decide (x.1.op = k.op ∧ x.1.key = k.key)) = none := by
    rw [List.find?_eq_none]
    intro x hx; simpa using hf x hx
  simp only [this, Option.none_or]
  simp [he]

/-- The world after `commit` holds the new receipt, found by a fresh key. -/
theorem commit_records (p : PlayerId) (wr : Write) (k : Keyed) (build : Game → Res) (w : World)
    (hfresh : Fresh p k w) (hwrote : (commit p wr (some k) build w).1 ≠ hidden ∨ ∃ g, wr = .insertGame g) :
    (ownReceipts p (commit p wr (some k) build w).2).find?
        (fun (x : ReceiptKey × Receipt) => x.1.op = k.op ∧ x.1.key = k.key) =
      some (⟨p, k.op, k.key⟩, Receipt.ofRes k.fingerprint (commit p wr (some k) build w).1) := by
  cases wr with
  | insertGame g =>
    simp only [commit, ownReceipts_record]
    have : ownReceipts p { w with games := w.games ++ [{ g with id := ⟨w.nextGame⟩ }], nextGame := w.nextGame + 1 } =
        ownReceipts p w := rfl
    rw [this]
    exact find_after_fresh hfresh ⟨rfl, rfl⟩
  | updateGame old new =>
    simp only [commit] at hwrote ⊢
    split
    · simp only [ownReceipts_record]
      have : ownReceipts p { w with games := w.games.map fun g => if g = old then new else g } =
          ownReceipts p w := rfl
      rw [this]
      exact find_after_fresh hfresh ⟨rfl, rfl⟩
    · rename_i hno
      simp [hno] at hwrote

/-- Resolution and authentication do not depend on the world's games. -/
theorem resolve_route_params {r : Req} {op : Op} {ps : List (String × String)}
    (h : Router.resolveIn entries .redirect r = .route op ps) :
    step r = operate op { r with params := ps } := by
  funext w; simp [step, h]

/-- **Keyed idempotence.** Let `r` be a request to a proved route that
    authenticates as `p`, carries an `Idempotency-Key` (so `i.keyed = some k`)
    with no earlier receipt, and whose first execution committed (its plan was
    a write that succeeded). Then sending `r` again returns the recorded
    response, marked as a replay, and leaves the world unchanged. -/
theorem keyed_replay (r : Req) (w : World) (p : PlayerId) (op : Op) (ps : List (String × String))
    (i : Input) (k : Keyed) (wr : Write) (build : Game → Res)
    (hroute : Router.resolveIn entries .redirect r = .route op ps)
    (hauth : authenticate { r with params := ps } w = .ok p)
    (hdec : decode op { r with params := ps } = .ok i)
    (hk : i.keyed = some k)
    (hfresh : Fresh p k w)
    (hplan : core p i (load p w i.need) = .write wr (some k) build)
    (hcommitted : (commit p wr (some k) build w).1 ≠ hidden ∨ ∃ g, wr = .insertGame g) :
    let (res, w') := step r w
    step r w' = (markReplay res, w') := by
  rw [resolve_route_params hroute]
  simp only [operate, hauth, hdec, hplan, runPlan]
  -- the second request authenticates the same (sessions unchanged by commit)
  have hs : (commit p wr (some k) build w).2.sessions = w.sessions := by
    cases wr with
    | insertGame g => simp [commit, (record_fields _ _ _ _).1]
    | updateGame old new =>
      simp only [commit]; split
      · exact (record_fields _ _ _ _).1
      · rfl
  have hauth' : authenticate { r with params := ps } (commit p wr (some k) build w).2 = .ok p := by
    rw [authenticate_view hs, hauth]
  simp only [hauth', hdec]
  have hrc := load_receipt p (commit p wr (some k) build w).2 i k _ hk (commit_records p wr k build w hfresh hcommitted)
  rw [core_replay p i _ k _ hk hrc rfl]
  simp [runPlan, Receipt.toRes, Receipt.ofRes]

/-! ## Reads do not change the world -/

theorem decideCore_read {p : PlayerId} {i : Input} {s : Slice}
    (h : i.keyed = none) (hr : ∀ w b, decideCore p i s ≠ .write w b) :
    ∃ res, core p i s = .respond res := by
  simp only [core, withReceipt, h]
  cases hd : decideCore p i s with
  | respond res => exact ⟨res, rfl⟩
  | write w b => exact absurd hd (hr w b)

theorem read_decide_respond (p : PlayerId) (i : Input) (s : Slice)
    (h : (∃ gid, i = .readGame gid) ∨ ∃ pg per, i = .listGames pg per) :
    ∃ res, core p i s = .respond res := by
  rcases h with ⟨gid, rfl⟩ | ⟨pg, per, rfl⟩
  · simp only [core, withReceipt, Input.keyed, decideCore]
    cases s.game <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem decode_read (op : Op) (r : Req) (i : Input) (hop : op = .readGame ∨ op = .listGames)
    (h : decode op r = .ok i) : (∃ gid, i = .readGame gid) ∨ ∃ pg per, i = .listGames pg per := by
  rcases hop with rfl | rfl
  · simp only [decode, runExtract] at h
    split at h
    · rename_i a ha
      cases h
      simp only [Functor.map, Except.map] at ha
      split at ha
      · cases ha
      · cases ha; exact .inl ⟨_, rfl⟩
    · cases h
  · simp only [decode, runExtract] at h
    split at h
    · rename_i a ha
      cases h
      simp only [bind, Except.bind] at ha
      split at ha
      · cases ha
      · split at ha
        · cases ha
        · split at ha
          · cases ha
          · cases ha; exact .inr ⟨_, _, rfl⟩
    · cases h

/-- **Reads are pure.** A request routed to `GET /games` or
    `GET /games/{id}` never changes the world, on any branch. -/
theorem reads_pure (r : Req) (w : World) (op : Op) (ps : List (String × String))
    (hroute : Router.resolveIn entries .redirect r = .route op ps)
    (hop : op = .readGame ∨ op = .listGames) : (step r w).2 = w := by
  rw [resolve_route_params hroute]
  simp only [operate]
  cases authenticate { r with params := ps } w with
  | error _ => rfl
  | ok p =>
    simp only
    cases hd : decode op { r with params := ps } with
    | error _ => rfl
    | ok i =>
      simp only
      obtain ⟨res, hres⟩ := read_decide_respond p i (load p w i.need) (decode_read op _ i hop hd)
      rw [hres]; rfl

/-- Unrouted requests (404, 405, OPTIONS, redirects) never change the world. -/
theorem unrouted_pure (r : Req) (w : World) (res : Res)
    (h : Router.resolveIn entries .redirect r = .respond res) : step r w = (res, w) := by
  simp [step, h]

/-! ## State idempotence of Resign, end to end -/

/-- Once `p` has resigned a game, an (unkeyed) resignation request by `p`
    for it answers with the game and changes nothing. -/
theorem resign_state_idem (p : PlayerId) (g : Game) (s : Slice)
    (hs : s.game = some g) (hr : g.resigned = some p) (hp : g.isParticipant p = true) (gid : GameId) :
    core p (.resign gid none) s = .respond (gameRes g) := by
  simp [core, withReceipt, Input.keyed, decideCore, hs, PrivateGames.resign, hp, hr]

/-! ## Availability -/

/-- A participant's read of a visible game succeeds (200 with the game), for
    any world containing it. The policy does not satisfy safety by refusing. -/
theorem read_available (p : PlayerId) (w : World) (g : Game) (gid : GameId)
    (hin : (visibleGames p w).find? (·.id = gid) = some g) :
    core p (.readGame gid) (load p w (Input.readGame gid).need) = .respond (gameRes g) := by
  simp [core, withReceipt, Input.keyed, decideCore, load, Input.need, hin]

theorem gameRes_status (g : Game) : (gameRes g).status = 200 := by
  simp [gameRes, Res.setHeader, Res.json]

end PrivateGames.Model
