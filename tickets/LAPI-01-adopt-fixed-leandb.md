# LAPI-01: Adopt the fixed LeanDB (M13): pin, proof update, public read snapshot

**Repo:** theoriclabs/leanapi · **Area:** `lakefile.toml`, `examples/private-games/PrivateGames/Storage` · **Priority:** P0 · **Size:** S
**Depends on:** a tagged LeanDB release with LDB-17…24 and the fixes from [the M13 review](../docs/reviews/2026-09-23-review-leandb-m13.md) (R1–R6, M1–M4). **Enables:** LAPI-02, LAPI-04.

## Problem

LeanAPI pins LeanDB `v0.4.0` (`lakefile.toml:16-18`), which has the bugs QUERIES.md §6 lists. The M13 fixes change two things LeanAPI depends on:

- **The `Nat` encoder.** LDB-18 routes `toCol` through `natToSql`. private-games' `nat_roundtrip` (`Storage/Schema.lean:30-35`) unfolds the old encoder and no longer builds. `cell_roundtrip` and `timeControl_roundtrip` rest on it, and all three are registered evidence (`Evidence.lean:116`).
- **The read snapshot.** LeanDB's deferred read transaction was private, so LeanAPI copied it as `Repo.readSnapshot` (`Storage/Repo.lean:178-208`), duplicating its nesting and poison-on-rollback-failure rules. LDB-24 publishes it.

Checked on 2026-09-23 against the unreleased M13 tip (`bdd0e4c`): with the proof updated, LeanAPI's whole CI passes, including the three-way differential test with the native service on the new LeanDB.

## Proposal

1. **Pin** the LeanDB release by tag, and run `lake update leandb`.
2. **Update `nat_roundtrip`** to prove the value fits before unfolding. The change was verified against `bdd0e4c`:
   ```lean
   have hmax : LeanDb.natSqlMax = 2^63 - 1 := by decide
   have hs : LeanDb.natToSql n = some (Int64.ofNat n) := by
     simp only [LeanDb.natToSql, hmax]; split <;> first | rfl | omega
   simp [ColCodec.fromCol, ColCodec.toCol, hs, h1, Int64.toNatClampNeg_ofNat_of_lt h]
   ```
   If the release changes `toCol` further (the review's R5 recommends it stop clamping), state the theorem against whatever encoder is published. Keep its meaning: values below 2^63 round-trip.
3. **Delete `Repo.readSnapshot`** and use `LeanDb.readSnapshot` in `Repo.readOn` and the list query (`Repo.lean:250`). It is used only on read-only connections, where the public version refuses writes (`.readOnly`). The review's M4 concerns the writer connection, which `readOn` never uses.
4. **Keep the repository's own connection workers** (`Repo.lean:210-244`: one thread per connection, the writer separate). private-games does not use `Runtime.Service`, so LDB-19's pool changes and its regressions (review R1, R2) don't reach it. Revisit after LAPI-05, when the runtime executes LeanDB programs.
5. **Record the version** in EVIDENCE.md's trusted base (item 6: "LeanDB and SQLite") and in CHANGELOG.

## Acceptance criteria

- `lakefile.toml` pins the LeanDB release by tag, and `lake-manifest.json` is updated.
- `Repo.readSnapshot` is gone; reads use `LeanDb.readSnapshot`.
- The whole CI passes: build, `leanapi_tests` (with the three-way differential test), axiom audit, README snippets, `gen_evidence.sh --check`.
- `nat_roundtrip`, `cell_roundtrip` and `timeControl_roundtrip` are still proved and registered.

## Tests

- **Out-of-range ids are refused before LeanDB.** The existing HTTP regressions for ids of 2^63 and above (review C2) still answer 422 at decoding. LDB-18's write-time refusal must stay unreachable from private-games, because `PlayerId.make`/`GameId.make` bound ids.
- **Snapshot consistency.** The list count and page (the "list count and page share a WAL snapshot" test) still agree when a writer commits between the two statements, now under `LeanDb.readSnapshot`.

## Compatibility

No HTTP behaviour changes. The differential test must agree before and after.
