/-
  Entity → system lift for list-shaped stores (PLAN.md M9, PROPERTIES.md §6.3
  "indexed conjunction").

  A `ListStore` is the domain-level view of a table: entities in a list, a
  counter for fresh ids, and two kinds of writer: `create` (build an entity
  with the next id) and `update` (replace an entity by the result of a
  decision). Given only per-entity facts, the library proves:

  * `allOf_inductive`: an entity invariant preserved by `create` and every
    command holds for every stored entity (the lift, no further proof);
  * `fresh_inductive`, `unique_rel`, `ids_invariant`: ids are unique. The
    strengthening `Fresh` (every id is below the counter) is what makes
    uniqueness inductive; this is the worked example of §6.5, and
    `unique_cti` shows uniqueness alone is not inductive.

  Apps relate their model to a store by a `Simulation` and pull these
  invariants back (see `PrivateGames/Model/Invariants.lean`).
-/
import LeanApi.Props.Ops

namespace LeanApi.Props

structure ListStore where
  Entity : Type
  /-- Arguments to create an entity (besides its id). -/
  Create : Type
  /-- A command applied to one entity (including the actor, if any). -/
  Cmd : Type
  Err : Type
  [deq : DecidableEq Entity]
  id : Entity → Nat
  create : Nat → Create → Except Err Entity
  apply : Cmd → Entity → Except Err Entity

namespace ListStore

variable (L : ListStore)

instance : DecidableEq L.Entity := L.deq

structure World where
  items : List L.Entity
  next : Nat

inductive Req where
  | create (c : L.Create)
  /-- Apply `c` to the stored entity equal to `target`. -/
  | update (target : L.Entity) (c : L.Cmd)

def replace (target new : L.Entity) (xs : List L.Entity) : List L.Entity :=
  xs.map fun x => if x = target then new else x

def step : L.Req → L.World → Except L.Err L.Entity × L.World
  | .create c, w =>
    match L.create w.next c with
    | .ok x => (.ok x, { items := w.items ++ [x], next := w.next + 1 })
    | .error e => (.error e, w)
  | .update t c, w =>
    match L.apply c t with
    | .ok y => (.ok y, { w with items := L.replace t y w.items })
    | .error e => (.error e, w)

/-- The store as a system with the given initial worlds. -/
def sysFrom (init : L.World → Prop) : Sys where
  World := L.World
  Req := L.Req
  Res := Except L.Err L.Entity
  Env := Unit
  step _ r w := L.step r w
  init := init

/-- The store starting empty; the counter may start anywhere. -/
abbrev sys : Sys := L.sysFrom (·.items = [])

/-! ## Entity invariants lift to the store -/

/-- Every stored entity satisfies `I`. -/
def AllOf (I : L.Entity → Prop) (w : L.World) : Prop := ∀ x ∈ w.items, I x

/-- The obligations for an entity invariant, one per writer kind. -/
structure Preserves (I : L.Entity → Prop) : Prop where
  create : ∀ n c x, L.create n c = .ok x → I x
  apply : ∀ c x y, I x → L.apply c x = .ok y → I y

theorem mem_replace {t y x : L.Entity} {xs : List L.Entity} (h : x ∈ L.replace t y xs) :
    x = y ∨ x ∈ xs := by
  simp only [replace, List.mem_map] at h
  obtain ⟨z, hz, rfl⟩ := h
  by_cases hzt : z = t <;> simp [hzt, hz]

theorem mem_replace_target {t y x : L.Entity} {xs : List L.Entity} (h : x ∈ L.replace t y xs) :
    (x = y ∧ t ∈ xs) ∨ x ∈ xs := by
  simp only [replace, List.mem_map] at h
  obtain ⟨z, hz, rfl⟩ := h
  by_cases hzt : z = t
  · subst hzt; simp [hz]
  · simp [hzt, hz]

/-- **The lift.** Per-entity obligations give the system invariant, from
    any initial worlds that satisfy it (a seeded database, for example). -/
theorem allOf_inductiveFrom {I : L.Entity → Prop} {init : L.World → Prop} (h : L.Preserves I)
    (hinit : ∀ w, init w → L.AllOf I w) : Inductive (L.sysFrom init) (L.AllOf I) := by
  refine ⟨hinit, fun _ r w hw => ?_⟩
  cases r with
  | create c =>
    show L.AllOf I (L.step (.create c) w).2
    simp only [step]
    split
    · rename_i x hx
      intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact hw z hz
      · exact h.create _ _ _ hx
    · exact hw
  | update t c =>
    show L.AllOf I (L.step (.update t c) w).2
    simp only [step]
    split
    · rename_i y hy
      intro z hz
      rcases L.mem_replace_target hz with ⟨rfl, ht⟩ | hz
      · exact h.apply c t z (hw t ht) hy
      · exact hw z hz
    · exact hw

theorem allOf_inductive {I : L.Entity → Prop} (h : L.Preserves I) : Inductive L.sys (L.AllOf I) :=
  L.allOf_inductiveFrom h fun w hw x hx => by simp [hw] at hx

theorem allOf_invariant {I : L.Entity → Prop} (h : L.Preserves I) : Invariant L.sys (L.AllOf I) :=
  Invariant.of_inductive (L.allOf_inductive h)

theorem allOf_invariantFrom {I : L.Entity → Prop} {init : L.World → Prop} (h : L.Preserves I)
    (hinit : ∀ w, init w → L.AllOf I w) : Invariant (L.sysFrom init) (L.AllOf I) :=
  Invariant.of_inductive (L.allOf_inductiveFrom h hinit)

/-! ## Unique ids, and the strengthening that makes them inductive -/

/-- Ids are unique. Not inductive by itself (`unique_cti`). -/
def UniqueIds (w : L.World) : Prop := (w.items.map L.id).Nodup

/-- Every id is below the counter: the missing conjunct a CTI names. -/
def Fresh (w : L.World) : Prop := ∀ x ∈ w.items, L.id x < w.next

/-- What the store's writers must satisfy for ids to be unique: `create`
    uses the id it is given, and commands never change an id. -/
structure IdLaws : Prop where
  create : ∀ n c x, L.create n c = .ok x → L.id x = n
  apply : ∀ c x y, L.apply c x = .ok y → L.id y = L.id x

theorem replace_ids {t y : L.Entity} (hid : L.id y = L.id t) (xs : List L.Entity) :
    (L.replace t y xs).map L.id = xs.map L.id := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [replace, List.map_cons] at ih ⊢
    rw [ih]; by_cases hx : x = t
    · subst hx; simp [hid]
    · simp [hx]

theorem fresh_inductiveFrom {init : L.World → Prop} (h : L.IdLaws) (hinit : ∀ w, init w → L.Fresh w) :
    Inductive (L.sysFrom init) L.Fresh := by
  refine ⟨hinit, fun _ r w hw => ?_⟩
  cases r with
  | create c =>
    show L.Fresh (L.step (.create c) w).2
    simp only [step]
    split
    · rename_i x hx
      intro z hz
      simp only [List.mem_append, List.mem_singleton] at hz
      rcases hz with hz | rfl
      · exact Nat.lt_succ_of_lt (hw z hz)
      · rw [h.create _ _ _ hx]; exact Nat.lt_succ_self _
    · exact hw
  | update t c =>
    show L.Fresh (L.step (.update t c) w).2
    simp only [step]
    split
    · rename_i y hy
      intro z hz
      rcases L.mem_replace_target hz with ⟨rfl, ht⟩ | hz
      · rw [h.apply c t z hy]; exact hw t ht
      · exact hw z hz
    · exact hw

theorem fresh_inductive (h : L.IdLaws) : Inductive L.sys L.Fresh :=
  L.fresh_inductiveFrom h fun w hw x hx => by simp [hw] at hx

/-- Uniqueness is inductive relative to `Fresh`. -/
theorem unique_relFrom {init : L.World → Prop} (h : L.IdLaws) (hinit : ∀ w, init w → L.UniqueIds w) :
    InductiveRel (L.sysFrom init) L.Fresh L.UniqueIds := by
  refine ⟨hinit, fun _ r w hf hu => ?_⟩
  cases r with
  | create c =>
    show L.UniqueIds (L.step (.create c) w).2
    simp only [step]
    split
    · rename_i x hx
      simp only [UniqueIds, List.map_append, List.map_cons, List.map_nil]
      rw [List.nodup_append]
      refine ⟨hu, by simp, ?_⟩
      intro a ha b hb hab
      simp only [List.mem_singleton] at hb
      obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
      have := hf z hz
      rw [hb, h.create _ _ _ hx] at hab
      omega
    · exact hu
  | update t c =>
    show L.UniqueIds (L.step (.update t c) w).2
    simp only [step]
    split
    · rename_i y hy
      simp only [UniqueIds]
      rw [L.replace_ids (h.apply c t y hy)]
      exact hu
    · exact hu

theorem unique_rel (h : L.IdLaws) : InductiveRel L.sys L.Fresh L.UniqueIds :=
  L.unique_relFrom h fun w hw => by simp [UniqueIds, hw]

theorem ids_inductiveFrom {init : L.World → Prop} (h : L.IdLaws)
    (hinit : ∀ w, init w → L.Fresh w ∧ L.UniqueIds w) :
    Inductive (L.sysFrom init) (fun w => L.Fresh w ∧ L.UniqueIds w) :=
  Inductive.and_rel (L.fresh_inductiveFrom h fun w hw => (hinit w hw).1)
    (L.unique_relFrom h fun w hw => (hinit w hw).2)

theorem ids_inductive (h : L.IdLaws) : Inductive L.sys (fun w => L.Fresh w ∧ L.UniqueIds w) :=
  Inductive.and_rel (L.fresh_inductive h) (L.unique_rel h)

theorem ids_invariant (h : L.IdLaws) : Invariant L.sys L.UniqueIds :=
  (Invariant.of_inductive (L.ids_inductive h)).mono fun _ h => h.2

theorem ids_invariantFrom {init : L.World → Prop} (h : L.IdLaws)
    (hinit : ∀ w, init w → L.Fresh w ∧ L.UniqueIds w) : Invariant (L.sysFrom init) L.UniqueIds :=
  (Invariant.of_inductive (L.ids_inductiveFrom h hinit)).mono fun _ h => h.2

/-- **Uniqueness alone is not inductive**, for any store whose `create`
    succeeds on some input: a world whose counter equals an existing id is
    a counterexample to induction. It is unreachable, which is why the fix
    is the strengthening `Fresh`, not a change to the code. -/
def unique_cti (c : L.Create) (x : L.Entity) (hx : L.create 0 c = .ok x) :
    CTI L.sys L.UniqueIds where
  world := { items := [x], next := 0 }
  env := ()
  req := .create c
  holds := by simp [UniqueIds]
  breaks := by
    show ¬ L.UniqueIds (L.step (.create c) _).2
    simp only [step, hx, UniqueIds, List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    simp

theorem unique_not_inductive (c : L.Create) (x : L.Entity) (hx : L.create 0 c = .ok x) :
    ¬ Inductive L.sys L.UniqueIds :=
  (L.unique_cti c x hx).not_inductive

/-- The CTI is exactly what `Fresh` rules out. -/
theorem unique_cti_excluded (h : L.IdLaws) (c : L.Create) (x : L.Entity) (hx : L.create 0 c = .ok x) :
    ¬ L.Fresh (L.unique_cti c x hx).world :=
  (L.unique_cti c x hx).excluded (J := L.Fresh)
    ⟨fun w hw => ((L.ids_inductive h).init w hw).symm,
     fun e r w hw => ((L.ids_inductive h).step e r w hw.symm).symm⟩

end ListStore

end LeanApi.Props
