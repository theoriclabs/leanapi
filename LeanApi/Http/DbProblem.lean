/-
  Problem defaults for LeanDB's typed write failures (LAPI-03).

  Every write failure type LeanDB derives from the schema (`InsertError`,
  `UpdateError`, `SetError`, `AppendError`, `DeleteError`) gets a
  `ToProblem` instance with a typed status and **no payload**: the holder
  of a clashing key, the current row after a lost compare-and-swap, and the
  referrers of a row are never in the default answer. Those payloads can
  reveal another user's data, so they are opt-in wrappers whose type says
  what they reveal:

  * `WithHolder (InsertError α)`: `Location` of the row holding the key;
  * `WithCurrent (UpdateError α)`: the current row's body and `ETag`;
  * `WithReferrers (DeleteError s α)`: which table still references the
    row, and how many rows.

  `ToProblem.Blind e` says which part of a failure the answer ignores. The
  defaults are blind to every payload (`*_blind`, by `rfl`); the wrappers
  are not (`WithHolder.not_blind`, a counterexample). The wrappers put
  their payload in the problem object (`location`, `current`/`etag`,
  `referrers`). So an isolation
  proof that goes through the default answer never needs the payload to be
  visible to the caller, and one that goes through a wrapper does.
-/
import LeanApi.Http.DbEndpoint

namespace LeanApi

open Lean LeanDb

/-- The column names of a unique index, for the detail (never its values). -/
private def ixName {α : Type} [Entity α] [HasUnique α] (ix : Unique α) : String :=
  ", ".intercalate (Unique.columns ix).toList

private def fkName {α : Type} [Entity α] [HasForeignKey α] (fk : ForeignKey α) : String :=
  Entity.fieldName (ForeignKey.field fk)

/-! ## Defaults -/

instance {α : Type} [Entity α] [HasUnique α] [HasForeignKey α] : ToProblem (InsertError α) where
  status
    | .duplicate .. => ⟨409, by decide⟩
    | .missingRef _ => ⟨422, by decide⟩
  detail
    | .duplicate ix _ => some s!"a row with this {ixName ix} already exists"
    | .missingRef _ => some "a referenced row does not exist"
  extensions
    | .duplicate .. => []
    | .missingRef fk => [("errors", Json.arr #[Json.mkObj
        [("loc", .str s!"body.{fkName fk}"), ("msg", .str "does not exist")]])]

instance {α : Type} [Entity α] [HasUnique α] [HasForeignKey α] : ToProblem (UpdateError α) where
  status
    | .stale _ => ⟨412, by decide⟩
    | .gone => ⟨404, by decide⟩
    | .duplicate .. => ⟨409, by decide⟩
    | .missingRef _ => ⟨422, by decide⟩
  detail
    | .stale _ => some "the resource changed since it was read"
    | .gone => none
    | .duplicate ix _ => some s!"a row with this {ixName ix} already exists"
    | .missingRef _ => some "a referenced row does not exist"
  extensions
    | .missingRef fk => [("errors", Json.arr #[Json.mkObj
        [("loc", .str s!"body.{fkName fk}"), ("msg", .str "does not exist")]])]
    | _ => []

instance {α : Type} [Entity α] [HasUnique α] [HasForeignKey α] (fs : LeanDb.Fields α) :
    ToProblem (SetError α fs) where
  status
    | .gone => ⟨404, by decide⟩
    | .duplicate .. => ⟨409, by decide⟩
    | .missingRef _ => ⟨422, by decide⟩
  detail
    | .gone => none
    | .duplicate t _ => some s!"a row with this {ixName t.ix} already exists"
    | .missingRef _ => some "a referenced row does not exist"
  extensions
    | .missingRef w => [("errors", Json.arr #[Json.mkObj
        [("loc", .str s!"body.{fkName w.fk}"), ("msg", .str "does not exist")]])]
    | _ => []

instance {α : Type} [Entity α] [HasListField α] : ToProblem (AppendError α) where
  status
    | .stale _ => ⟨412, by decide⟩
    | .gone => ⟨404, by decide⟩
    | .notAppend _ => ⟨409, by decide⟩
  detail
    | .stale _ => some "the resource changed since it was read"
    | .gone => none
    | .notAppend l => some s!"{HasListField.table l} can only grow"

instance {s α : Type} [Entity α] [HasReferencedBy s α] : ToProblem (DeleteError s α) where
  status
    | .gone => ⟨404, by decide⟩
    | .restricted .. => ⟨409, by decide⟩
  detail
    | .gone => none
    | .restricted .. => some "the resource is still referenced"

/-! ## Blindness: what the default answer ignores -/

/-- Two failures related by `same` (typically: equal but for a payload)
    give the same problem object, hence the same response
    (`Blind.toRes`). -/
def ToProblem.Blind {ε : Type} [ToProblem ε] (same : ε → ε → Prop) : Prop :=
  ∀ e₁ e₂, same e₁ e₂ → ToProblem.problem e₁ = ToProblem.problem e₂

theorem ToProblem.Blind.toRes {ε : Type} [ToProblem ε] {same : ε → ε → Prop}
    (h : ToProblem.Blind same) {e₁ e₂ : ε} (hs : same e₁ e₂) :
    ToResponse.toRes (Except.error e₁ : Except ε Unit) = ToResponse.toRes (Except.error e₂ : Except ε Unit) := by
  show (ToProblem.problem e₁).toRes = (ToProblem.problem e₂).toRes
  rw [h e₁ e₂ hs]

section blind
variable {α : Type} [Entity α] [HasUnique α] [HasForeignKey α]

/-- Equal, except perhaps for the holder of a clashing key. -/
def InsertError.SameButHolder : InsertError α → InsertError α → Prop
  | .duplicate i₁ _, .duplicate i₂ _ => i₁ = i₂
  | e₁, e₂ => e₁ = e₂

/-- The default insert answer does not depend on the holder. -/
theorem InsertError.blind_holder :
    ToProblem.Blind (InsertError.SameButHolder (α := α)) := by
  intro e₁ e₂ h
  cases e₁ <;> cases e₂ <;> simp only [InsertError.SameButHolder] at h <;>
    first | rfl | (subst h; rfl) | (cases h; rfl) | (cases h)

/-- The default update answer depends on neither the current row nor the
    holder. -/
def UpdateError.SameButPayload : UpdateError α → UpdateError α → Prop
  | .stale _, .stale _ => True
  | .duplicate i₁ _, .duplicate i₂ _ => i₁ = i₂
  | e₁, e₂ => e₁ = e₂

theorem UpdateError.blind_payload :
    ToProblem.Blind (UpdateError.SameButPayload (α := α)) := by
  intro e₁ e₂ h
  cases e₁ <;> cases e₂ <;> simp only [UpdateError.SameButPayload] at h <;>
    first | rfl | (subst h; rfl) | (cases h; rfl) | (cases h)

end blind

/-- The default delete answer does not say who references the row. -/
def DeleteError.SameButReferrers {s α : Type} [Entity α] [HasReferencedBy s α] :
    DeleteError s α → DeleteError s α → Prop
  | .restricted .., .restricted .. => True
  | e₁, e₂ => e₁ = e₂

theorem DeleteError.blind_referrers {s α : Type} [Entity α] [HasReferencedBy s α] :
    ToProblem.Blind (DeleteError.SameButReferrers (s := s) (α := α)) := by
  intro e₁ e₂ h
  cases e₁ <;> cases e₂ <;> simp only [DeleteError.SameButReferrers] at h <;>
    first | rfl | (cases h)

/-! ## Opt-in payloads -/

/-- Where a row lives, for `Location`. -/
class LocationOf (α : Type) where
  location : LeanDb.Id α → String

/-- `InsertError α`, answering with the holder's `Location` on a clash.
    Reveals that the holder exists and holds the key. -/
structure WithHolder (ε : Type) where
  val : ε

instance {α : Type} [Entity α] [HasUnique α] [HasForeignKey α] [LocationOf α] :
    ToProblem (WithHolder (InsertError α)) where
  status e := ToProblem.status e.val
  detail e := ToProblem.detail e.val
  extensions e := match e.val with
    | .duplicate _ holder => [("location", .str (LocationOf.location holder))]
    | e => ToProblem.extensions e

/-- The holder wrapper is **not** blind: two clashes on the same index whose
    holders live at different places answer differently. An isolation
    proof through `WithHolder` therefore needs the holder in the caller's
    view. -/
theorem WithHolder.not_blind {α : Type} [Entity α] [HasUnique α] [HasForeignKey α] [LocationOf α]
    (ix : Unique α) (h₁ h₂ : LeanDb.Id α) (hne : LocationOf.location h₁ ≠ LocationOf.location h₂) :
    ¬ ToProblem.Blind (fun e₁ e₂ : WithHolder (InsertError α) => InsertError.SameButHolder e₁.val e₂.val) := by
  intro hb
  have h := congrArg Problem.extensions (hb ⟨.duplicate ix h₁⟩ ⟨.duplicate ix h₂⟩ rfl)
  have e : ∀ h' : LeanDb.Id α, ToProblem.extensions (ε := WithHolder (InsertError α)) ⟨.duplicate ix h'⟩ =
      [("location", .str (LocationOf.location h'))] := fun _ => rfl
  simp only [ToProblem.problem, e, List.foldl, Problem.withExt] at h
  simp at h
  exact hne h.2

/-- A version for `ETag`. -/
class VersionOf (α : Type) where
  version : α → String

/-- `UpdateError α`, answering a lost compare-and-swap with the current row
    and its version. Reveals the row. -/
structure WithCurrent (ε : Type) where
  val : ε

instance {α : Type} [Entity α] [HasUnique α] [HasForeignKey α] [ToJson α] [VersionOf α] :
    ToProblem (WithCurrent (UpdateError α)) where
  status e := ToProblem.status e.val
  detail e := ToProblem.detail e.val
  extensions e := match e.val with
    | .stale cur => [("current", toJson cur.val), ("etag", .str (VersionOf.version cur.val))]
    | e => ToProblem.extensions e

/-- `DeleteError s α`, naming the referencing table and the row count.
    Reveals that such rows exist. -/
structure WithReferrers (ε : Type) where
  val : ε

instance {s α : Type} [Entity α] [h : HasReferencedBy s α] [Repr (ReferencedBy.Restricting s α)] :
    ToProblem (WithReferrers (DeleteError s α)) where
  status e := ToProblem.status e.val
  detail e := ToProblem.detail e.val
  extensions e := match e.val with
    | .restricted who n => [("referrers", Json.mkObj [("by", .str (reprStr who)), ("rows", toJson n)])]
    | _ => []

end LeanApi
