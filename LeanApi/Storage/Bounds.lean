import LeanDb

namespace LeanApi.Storage

/-- A genuine SQLite range proof for existing bounded domain values. -/
theorem nat_sql_range (value : Nat) (bounded : value < 2 ^ 63) :
    (LeanDb.ColCodec.toSql? value).isSome = true := by
  change ((LeanDb.natToSql value).map LeanDb.Col.int).isSome = true
  have maximum : LeanDb.natSqlMax = 2 ^ 63 - 1 := by decide
  simp only [LeanDb.natToSql, maximum]
  split <;> first | rfl | omega

end LeanApi.Storage
