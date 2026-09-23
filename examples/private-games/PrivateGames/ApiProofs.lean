/-
  Theorems about the typed private-games API (`PrivateGames/Api.lean`),
  through the framework's generic results for typed APIs:

  * `api_reads_safe`: GET and HEAD never change the state. No proof here:
    it is `Api.step_safe`, which every typed API has.
  * `api_allValid`, `api_uniqueIds`, `api_freshIds`: every stored game is
    `Valid`, ids are unique, and every id is below `nextGame`, in every
    reachable state. By `Api.inductive_of`, the obligation is per endpoint
    and computed from its signature: nothing for the two `Reads` endpoints;
    for each `Writes` endpoint, that its state function preserves the
    invariant. Each is discharged by showing the write is a step of the
    generic game store, whose writers are the domain decisions, so the
    invariant rests on the domain's `preserves` theorems.
-/
import PrivateGames.Api
import PrivateGames.Model.Invariants

namespace PrivateGames.Api

open LeanApi LeanApi.Props PrivateGames PrivateGames.App PrivateGames.Model

/-- The typed API as a transition system, starting with no games. -/
def apiSys : Sys := gamesApi.toSys gamesInit

/-! ## GET is safe, for free -/

theorem api_reads_safe (env : Env) (r : Req) (w : World) (hm : r.method.Safe) :
    (gamesApi.step env r w).2 = w :=
  Api.step_safe gamesApi env r w hm

/-! ## Writes are steps of the game store -/

/-- `w'` is `w` as far as games go, or one step of the game store after it. -/
def StoreStep (w w' : World) : Prop :=
  toStore w' = toStore w ∨ ∃ r, toStore w' = (gameStore.step r (toStore w)).2

theorem StoreStep.refl (w : World) : StoreStep w w := .inl rfl

/-- The store invariant: every game valid, ids fresh and unique. -/
def StoreInv (st : gameStore.World) : Prop :=
  gameStore.AllOf Valid st ∧ (gameStore.Fresh st ∧ gameStore.UniqueIds st)

theorem storeInv_inductive : Inductive gameStore.sys StoreInv :=
  Inductive.and (gameStore.allOf_inductive gameStore_preserves) (gameStore.ids_inductive gameStore_idLaws)

theorem StoreStep.preserves {w w' : World} (h : StoreStep w w') (hi : StoreInv (toStore w)) :
    StoreInv (toStore w') := by
  rcases h with h | ⟨r, h⟩
  · rw [h]; exact hi
  · rw [h]; exact storeInv_inductive.step () r _ hi

/-- A decision whose writes are store steps gives a keyed write whose
    result is a store step: receipts do not touch the games. -/
theorem keyed_storeStep [ToResponse α] (me : PlayerId) (k? : Option Keyed) (decide : World → Decided α)
    (hd : ∀ w w' a, decide w = .write w' a → StoreStep w w') (w : World) :
    StoreStep w (keyed me k? decide w).1 := by
  unfold keyed
  split
  · exact .refl w
  · split
    · exact .refl w
    · exact .refl w
    · rename_i w' a hw
      have := hd w w' a hw
      rcases this with h | ⟨r, h⟩
      · exact .inl (by rw [toStore_record, h])
      · exact .inr ⟨r, by rw [toStore_record, h]⟩

theorem replace_storeStep (w : World) (g g' : Game) (c : gameStore.Cmd)
    (hc : PrivateGames.decide c.1 g c.2 = .ok g') :
    StoreStep w (replaceGame w g g') := by
  refine .inr ⟨.update g c, ?_⟩
  simp only [toStore, replaceGame, ListStore.step, gameStore, hc, ListStore.replace]
  congr 2

theorem openGame_storeStep (me : Auth PlayerId) (body : Body OpenBody) (key : KeyHeader) (w : World) :
    StoreStep w (openGame me body key w).1 := by
  apply keyed_storeStep
  intro w w' a h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i g hg
      cases h
      refine .inr ⟨.create (me.val, body.val.opponent, body.val.tc), ?_⟩
      simp only [toStore, ListStore.step, gameStore, hg]
      rfl

theorem playMove_storeStep (me : Auth PlayerId) (rev : IfMatchRequired ETagRev) (body : Body MoveBody)
    (id : Path GameId) (key : KeyHeader) (w : World) :
    StoreStep w (playMove me rev body id key w).1 := by
  apply keyed_storeStep
  intro w w' a h
  split at h
  · cases h
  · rename_i g _
    split at h
    · cases h
    · cases h
    · rename_i g' hg
      cases h
      exact replace_storeStep w g g' (me.val, .play rev.val.rev body.val.cell) hg

theorem resign_storeStep (me : Auth PlayerId) (id : Path GameId) (key : KeyHeader) (w : World) :
    StoreStep w (resign me id key w).1 := by
  apply keyed_storeStep
  intro w w' a h
  split at h
  · cases h
  · rename_i g _
    split at h
    · cases h
    · cases h
    · rename_i g' hg
      split at h
      · cases h
      · cases h
        exact replace_storeStep w g g' (me.val, .resign) hg

/-! ## The invariants, through `Api.inductive_of` -/

/-- Every endpoint discharges its `Preserved` obligation. -/
theorem api_preserved : ∀ e ∈ gamesApi, e.Preserved (fun w => StoreInv (toStore w)) := by
  intro e he
  simp only [gamesApi, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact fun me body key w hi => (openGame_storeStep ⟨me⟩ body key w).preserves hi
  · exact fun _ _ => trivial
  · exact fun _ _ => trivial
  · exact fun me rev body id key w hi => (playMove_storeStep ⟨me⟩ rev body ⟨id⟩ key w).preserves hi
  · exact fun me id key w hi => (resign_storeStep ⟨me⟩ ⟨id⟩ key w).preserves hi

theorem api_inductive : Inductive apiSys (fun w => StoreInv (toStore w)) :=
  Api.inductive_of gamesApi (fun w hw => storeInv_inductive.init _ hw) api_preserved

/-- **Every stored game is `Valid`**, in every reachable state of the typed API. -/
theorem api_allValid : Invariant apiSys (fun w => ∀ g ∈ w.games, Valid g) :=
  (Invariant.of_inductive api_inductive).mono fun _ h => h.1

/-- **Game ids are unique**, in every reachable state of the typed API. -/
theorem api_uniqueIds : Invariant apiSys (fun w => (w.games.map (·.id.n)).Nodup) :=
  (Invariant.of_inductive api_inductive).mono fun _ h => h.2.2

/-- Every id is below `nextGame` (the strengthening uniqueness needs). -/
theorem api_freshIds : Invariant apiSys (fun w => ∀ g ∈ w.games, g.id.n < w.nextGame) :=
  (Invariant.of_inductive api_inductive).mono fun _ h => h.2.1

end PrivateGames.Api
