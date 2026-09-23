/-
  System-level invariants of private-games, proved through the property
  kernel (PLAN.md M8 demonstrator). Until now these were only checked at
  runtime by the repository:

  1. `allValid`: every stored game is `Valid`.
  2. `uniqueIds`: game ids are unique. This needs the strengthening
     `Fresh` (every id is below `nextGame`), found as the counterexample to
     induction `ListStore.unique_cti` (PROPERTIES.md §6.5).

  How: the model (`gamesApp.toSys`) simulates the generic `ListStore` of
  games. The simulation obligation is the only app-specific proof, and it
  is a fact about `core`: every insert it plans is a valid game, and every
  update keeps the game's id. The library then gives both invariants.
-/
import LeanApi.Props.Bridge
import LeanApi.Props.Store
import PrivateGames.Model.Generic

namespace PrivateGames.Model

open LeanApi LeanApi.Props LeanApi.Proofs PrivateGames.App

/-! ## The store of games -/

/-- Games as a generic list store. `create` refuses invalid games, and an
    update may only replace a game by a valid game with the same id. -/
def gameStore : ListStore where
  Entity := Game
  Create := Game
  Cmd := Game
  Err := Unit
  id g := g.id.n
  create n g := if Valid g then .ok { g with id := ⟨n⟩ } else .error ()
  apply new old := if new.id = old.id ∧ Valid new then .ok new else .error ()

theorem gameStore_preserves : gameStore.Preserves Valid where
  create n c x h := by
    simp only [gameStore] at h
    split at h
    · cases h; rename_i hv; exact ⟨hv.1, hv.2, hv.3, hv.4, hv.5, hv.6⟩
    · cases h
  apply c x y _ h := by
    simp only [gameStore] at h
    split at h
    · cases h; rename_i hv; exact hv.2
    · cases h

theorem gameStore_idLaws : gameStore.IdLaws where
  create n c x h := by
    simp only [gameStore] at h
    split at h
    · cases h; rfl
    · cases h
  apply c x y h := by
    simp only [gameStore] at h
    split at h
    · cases h; rename_i hv; exact congrArg GameId.n hv.1
    · cases h

/-! ## What `core` plans -/

/-- The writes `core` may plan: valid inserts, id-preserving updates. -/
def WriteOk : Write → Prop
  | .insertGame g => Valid g
  | .updateGame old new => new.id = old.id

theorem playMove_id {p : PlayerId} {e : Revision} {c : Cell} {g g' : Game}
    (h : PrivateGames.playMove p e c g = .ok g') : g'.id = g.id := by
  obtain ⟨_, _, _, _, _, rfl⟩ := playMove_ok h; rfl

theorem resign_id {p : PlayerId} {g g' : Game} (h : PrivateGames.resign p g = .ok g') : g'.id = g.id := by
  obtain ⟨_, hc⟩ := resign_ok h
  rcases hc with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

theorem decideCore_writeOk {p : PlayerId} {i : Input} {s : Slice} {wr : Write} {b : Game → Res}
    (h : decideCore p i s = .write wr b) : WriteOk wr := by
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
      · rename_i g _ g' hg; cases h; exact playMove_id hg
  | resign _ _ =>
    simp only [decideCore] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i g _ g' hg
        split at h
        · cases h
        · cases h; exact resign_id hg

theorem core_writeOk {p : PlayerId} {i : Input} {s : Slice} {wr : Write} {k : Option Keyed} {b : Game → Res}
    (h : core p i s = .write wr k b) : WriteOk wr := by
  simp only [core, withReceipt] at h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h
    · rename_i wr' b' hd; cases h; exact decideCore_writeOk hd

/-! ## The simulation -/

def toStore (w : World) : gameStore.World := { items := w.games, next := w.nextGame }

/-- The model world starts with no games. Sessions, players and receipts
    may start anywhere. -/
def gamesInit (w : World) : Prop := w.games = []

def gamesSys : Sys := gamesApp.toSys gamesInit

theorem toStore_record (p : PlayerId) (k : Option Keyed) (res : Res) (w : World) :
    toStore (recordReceipt p k res w) = toStore w := by
  cases k <;> rfl

theorem commit_sim (p : PlayerId) (wr : Write) (k : Option Keyed) (b : Game → Res) (w : World)
    (hw : WriteOk wr) :
    toStore (commit p wr k b w).2 = toStore w ∨
      ∃ r, toStore (commit p wr k b w).2 = (gameStore.step r (toStore w)).2 := by
  cases wr with
  | insertGame g =>
    refine .inr ⟨.create g, ?_⟩
    have hv : Valid g := hw
    simp only [commit, toStore_record]
    simp [toStore, ListStore.step, gameStore, hv] <;> rfl
  | updateGame old new =>
    simp only [commit]
    split
    · rename_i hok
      refine .inr ⟨.update old new, ?_⟩
      have hid : new.id = old.id := hw
      simp only [commitOk, Bool.and_eq_true, beq_iff_eq] at hok
      have hv : Valid new := (Valid.holdsB_iff new).mp hok.1.1.2
      rw [toStore_record]
      simp [toStore, ListStore.step, gameStore, hid, hv, ListStore.replace]
      intro _ _; rfl
    · exact .inl rfl

theorem gamesSys_sim : Simulation gamesSys gameStore.sys toStore where
  init w h := h
  step e r w := by
    show toStore (gamesApp.step r w).2 = toStore w ∨
      ∃ e' r', toStore (gamesApp.step r w).2 = (gameStore.step r' (toStore w)).2
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
          change toStore (runPlan p (core p i (load p w i.need)) w).2 = toStore w ∨
            ∃ e' r', toStore (runPlan p (core p i (load p w i.need)) w).2 = (gameStore.step r' (toStore w)).2
          cases hc : core p i (load p w i.need) with
          | respond _ => exact .inl rfl
          | write wr k b =>
            rcases commit_sim p wr k b w (core_writeOk hc) with h | ⟨r', h⟩
            · exact .inl h
            · exact .inr ⟨(), r', h⟩

/-! ## The two invariants -/

/-- **Every stored game is `Valid`**, in every reachable world of the model.
    The only app-specific proof is `core_writeOk`; the rest is the library's
    entity → store lift and pullback along the simulation. -/
theorem allValid : Invariant gamesSys (fun w => ∀ g ∈ w.games, Valid g) :=
  Invariant.pullback gamesSys_sim (gameStore.allOf_invariant gameStore_preserves)

/-- **Game ids are unique**, in every reachable world of the model. -/
theorem uniqueIds : Invariant gamesSys (fun w => (w.games.map (·.id.n)).Nodup) :=
  Invariant.pullback gamesSys_sim (gameStore.ids_invariant gameStore_idLaws)

/-- The strengthening is itself invariant: every id is below `nextGame`. -/
theorem freshIds : Invariant gamesSys (fun w => ∀ g ∈ w.games, g.id.n < w.nextGame) :=
  Invariant.pullback gamesSys_sim (Invariant.of_inductive (gameStore.fresh_inductive gameStore_idLaws))

/-- Uniqueness alone is not inductive for the store of games: the kernel's
    `CTI` names the world (`nextGame` equal to an existing id), and `Fresh`
    excludes it. -/
theorem uniqueIds_needs_fresh : ¬ Inductive gameStore.sys gameStore.UniqueIds := by
  have hv : Valid (Game.opened ⟨0⟩ ⟨1⟩ ⟨2⟩ TimeControl.default) := by decide
  exact gameStore.unique_not_inductive (Game.opened ⟨0⟩ ⟨1⟩ ⟨2⟩ TimeControl.default) _
    (by simp only [gameStore, hv]; rfl)

end PrivateGames.Model
