/-
  Generic keyed idempotence (PLAN.md M12, PROPERTIES.md §4.3(c)).

  `Keyed S` wraps any system with a receipt ledger. A keyed request is
  scoped by the library (`scope r`, typically actor and operation) and
  identified by a fingerprint of its canonical input (`fp r`):

  * no receipt for the key: run `S`, record `(fp, response)`;
  * a receipt with the same fingerprint: replay it, change nothing;
  * a receipt with another fingerprint: refuse, change nothing.

  Proved once, for any `S` and any ledger satisfying `LedgerLaws`:

  * `keyed_stable`: once recorded, a receipt is never changed by any
    request, keyed or not (a step property);
  * `keyed_replay_after`: after a keyed request commits, replaying it after
    **any** sequence of intervening requests returns the recorded response
    and changes nothing;
  * `keyed_reuse`: reusing a key with a different input is refused and
    changes nothing;
  * `keyed_scoped`: a key recorded under one scope is invisible under
    another, so a response is never replayed to another actor.

  `listLedger` (append, first match) satisfies `LedgerLaws`; it is the
  model of the receipt table private-games uses.
-/
import LeanApi.Props.Shapes

namespace LeanApi.Props

/-- A receipt ledger over keys `K` and values `V`. -/
structure Ledger (K V : Type) where
  L : Type
  lookup : L → K → Option V
  record : L → K → V → L

/-- What any ledger implementation must satisfy. `record` is only ever
    called for a key with no receipt. -/
structure LedgerLaws {K V : Type} (led : Ledger K V) : Prop where
  lookup_record_same : ∀ l k v, led.lookup l k = none → led.lookup (led.record l k v) k = some v
  lookup_record_other : ∀ l k k' v, k' ≠ k → led.lookup (led.record l k v) k' = led.lookup l k'

/-- The list ledger: append a receipt, look up the first match. -/
def listLedger (K V : Type) [DecidableEq K] : Ledger K V where
  L := List (K × V)
  lookup l k := (l.find? (·.1 = k)).map (·.2)
  record l k v := l ++ [(k, v)]

theorem listLookup_record_same {K V : Type} [DecidableEq K] (l : List (K × V)) (k : K) (v : V)
    (h : (l.find? (·.1 = k)).map (·.2) = none) : ((l ++ [(k, v)]).find? (·.1 = k)).map (·.2) = some v := by
  simp only [Option.map_eq_none_iff] at h
  rw [List.find?_append, h]; simp

theorem listLookup_record_other {K V : Type} [DecidableEq K] (l : List (K × V)) (k k' : K) (v : V)
    (hne : k' ≠ k) : ((l ++ [(k, v)]).find? (·.1 = k')).map (·.2) = (l.find? (·.1 = k')).map (·.2) := by
  rw [List.find?_append]
  cases hf : l.find? (fun x => decide (x.1 = k')) with
  | some _ => simp
  | none =>
    have : [(k, v)].find? (fun x => decide (x.1 = k')) = none := by simp [Ne.symm hne]
    simp [this]

theorem listLedger_laws (K V : Type) [DecidableEq K] : LedgerLaws (listLedger K V) :=
  ⟨listLookup_record_same, fun l k k' v hne => listLookup_record_other l k k' v hne⟩

/-- Responses of the keyed system. -/
inductive KRes (R : Type) where
  | fresh (r : R)
  | replay (r : R)
  | keyReused

/-- The keyed transformer. `Scope` and `Fp` are the scope of a key and the
    fingerprint of an input; `scope` and `fp` are computed from the request,
    so the app cannot scope a key wrongly. -/
def Keyed (S : Sys) {Scope Fp : Type} [DecidableEq Fp] (scope : S.Req → Scope) (fp : S.Req → Fp)
    (led : Ledger (Scope × String) (Fp × S.Res)) : Sys where
  World := S.World × led.L
  Req := S.Req × Option String
  Res := KRes S.Res
  Env := S.Env
  step e r w :=
    match r.2 with
    | none => let (res, w') := S.step e r.1 w.1; (.fresh res, (w', w.2))
    | some key =>
      let k := (scope r.1, key)
      match led.lookup w.2 k with
      | some (f, res) => if f = fp r.1 then (.replay res, w) else (.keyReused, w)
      | none => let (res, w') := S.step e r.1 w.1; (.fresh res, (w', led.record w.2 k (fp r.1, res)))
  init w := S.init w.1

namespace Keyed

variable {S : Sys} {Scope Fp : Type} [DecidableEq Fp]
  {scope : S.Req → Scope} {fp : S.Req → Fp} {led : Ledger (Scope × String) (Fp × S.Res)}

/-- **Receipts are stable**: a recorded receipt survives every request. -/
theorem keyed_stable (hl : LedgerLaws led) {k : Scope × String} {v : Fp × S.Res}
    (e : S.Env) (r : (Keyed S scope fp led).Req) (w : (Keyed S scope fp led).World)
    (h : led.lookup w.2 k = some v) : led.lookup ((Keyed S scope fp led).step e r w).2.2 k = some v := by
  obtain ⟨r, key?⟩ := r
  cases key? with
  | none => exact h
  | some key =>
    simp only [Keyed]
    cases hk : led.lookup w.2 (scope r, key) with
    | some fr =>
      obtain ⟨f, res⟩ := fr
      simp only
      split <;> exact h
    | none =>
      simp only
      have hne : k ≠ (scope r, key) := fun heq => by rw [heq] at h; rw [h] at hk; cases hk
      rw [hl.lookup_record_other _ _ _ _ hne]; exact h

/-- Run a sequence of requests. -/
def run (S : Sys) : List (S.Env × S.Req) → S.World → S.World
  | [], w => w
  | (e, r) :: rs, w => run S rs (S.step e r w).2

theorem keyed_stable_run (hl : LedgerLaws led) {k : Scope × String} {v : Fp × S.Res}
    (rs : List (S.Env × (Keyed S scope fp led).Req)) (w : (Keyed S scope fp led).World)
    (h : led.lookup w.2 k = some v) : led.lookup (run _ rs w).2 k = some v := by
  induction rs generalizing w with
  | nil => exact h
  | cons x rs ih => exact ih _ (keyed_stable hl x.1 x.2 w h)

/-- A request with a recorded, matching receipt replays it and changes
    nothing (neither the app's world nor the ledger). -/
theorem keyed_replay (r : S.Req) (key : String) (e : S.Env) (w : (Keyed S scope fp led).World)
    (res : S.Res) (h : led.lookup w.2 (scope r, key) = some (fp r, res)) :
    (Keyed S scope fp led).step e (r, some key) w = (.replay res, w) := by
  simp [Keyed, h]

/-- The first keyed request with a fresh key runs `S` and records it. -/
theorem keyed_first (hl : LedgerLaws led) (r : S.Req) (key : String) (e : S.Env)
    (w : (Keyed S scope fp led).World) (h : led.lookup w.2 (scope r, key) = none) :
    let out := (Keyed S scope fp led).step e (r, some key) w
    out.1 = .fresh (S.step e r w.1).1 ∧ out.2.1 = (S.step e r w.1).2 ∧
      led.lookup out.2.2 (scope r, key) = some (fp r, (S.step e r w.1).1) := by
  simp only [Keyed, h]
  exact ⟨trivial, trivial, hl.lookup_record_same _ _ _ h⟩

/-- **Keyed idempotence after any interleaving.** Send a keyed request with
    a fresh key, then any sequence of requests (keyed or not, from anyone),
    then the same keyed request again: the second answer is the first
    response, marked as a replay, and nothing changes. -/
theorem keyed_replay_after (hl : LedgerLaws led) (r : S.Req) (key : String) (e e' : S.Env)
    (w : (Keyed S scope fp led).World) (h : led.lookup w.2 (scope r, key) = none)
    (between : List (S.Env × (Keyed S scope fp led).Req)) :
    let first := (Keyed S scope fp led).step e (r, some key) w
    let wn := run _ between first.2
    (Keyed S scope fp led).step e' (r, some key) wn = (.replay (S.step e r w.1).1, wn) := by
  intro first wn
  obtain ⟨_, _, hrec⟩ := keyed_first hl r key e w h
  exact keyed_replay r key e' wn _ (keyed_stable_run hl between first.2 hrec)

/-- Reusing a key with a different input is refused, and changes nothing. -/
theorem keyed_reuse (r : S.Req) (key : String) (e : S.Env) (w : (Keyed S scope fp led).World)
    (f : Fp) (res : S.Res) (h : led.lookup w.2 (scope r, key) = some (f, res)) (hf : f ≠ fp r) :
    (Keyed S scope fp led).step e (r, some key) w = (.keyReused, w) := by
  simp [Keyed, h, hf]

omit [DecidableEq Fp] in
/-- Scopes separate keys: recording under `(s, key)` does not create a
    receipt visible under another scope `s'` with the same key string. -/
theorem keyed_scoped (hl : LedgerLaws led) (l : led.L) {s s' : Scope} (key : String) (v : Fp × S.Res)
    (hs : s' ≠ s) : led.lookup (led.record l (s, key) v) (s', key) = led.lookup l (s', key) :=
  hl.lookup_record_other _ _ _ _ (fun h => hs (Prod.mk.inj h).1)

end Keyed

end LeanApi.Props
