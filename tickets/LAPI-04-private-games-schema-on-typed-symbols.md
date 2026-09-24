# LAPI-04: private-games schema on typed symbols: `unique`, `schema`, `Checked` from proofs

**Repo:** theoriclabs/leanapi · **Area:** `examples/private-games/PrivateGames/Storage/Schema.lean` · **Priority:** P0 · **Size:** S
**Depends on:** LeanDB M14 (`unique` declarations, generated `Unique`/`ForeignKey`/`ListField`/`ReferencedBy`, the `schema` command, `Checked`). **Enables:** LAPI-05.

## Problem

private-games declares its unique indexes as string lists:
- `PlayerRow`: `columns := #["name"]` (`Schema.lean:55`);
- `TokenRow`: `#["digest"]` (`:62`);
- `ReceiptRow`: `#["actor", "op", "key"]` (`:92-93`).

Its game invariant is checked at runtime by the repository (`Schema.lean:113-115`, `Valid.stored.guardLoad`/`guardWrite`). With LeanDB M14, these become typed:
- unique indexes generate `Unique α` constructors with key types, which the failure types of writes mention;
- writes take `Checked α`.

That is what lets `gamesApi` (LAPI-05) have exact failure types, and lets the invariant be established by proof rather than by a runtime check.

## Proposal

1. **Declare the unique indexes:**
   ```lean
   unique PlayerRow.byName  := name
   unique TokenRow.byDigest := digest
   unique ReceiptRow.byKey  := (actor, op, key)
   ```
   Keep non-unique indexes (`GameRow`, `Schema.lean:77-80`) as `Indexes` entries. They do not appear in failure types.
2. **Declare the schema:** `schema Games := PlayerRow, TokenRow, GameRow, ReceiptRow`. This gives `ReferencedBy Games PlayerRow`: games (`x`, `o`, `resigned`), tokens (`player`) and receipts (`actor`).
3. **`GameRow`'s invariant is the domain's `Valid`, through the row mapping** (`GameRow.toGame`, `Schema.lean:~100`): `GameRow.Invariant r := Valid (r.toGame ⟨0⟩)`. Validity does not depend on the id, and a lemma should say so (`Valid (r.toGame i) ↔ Valid (r.toGame j)`).
   - `Checked GameRow` for a new or changed game is built **from the domain proof** (`Checked.of`, using `Valid.preserved_openGame`/`_playMove`/`_resign`), not by a runtime check.
   - A lemma `toGame_ofGame : (ofGame g).toGame g.id = g`, with the existing codec round-trips, connects them.
4. **Keep a runtime check only where values come from outside the proofs:** decoding a stored row. LeanDB's own read-time invariant check (LDB-16) replaces `reconstruct`'s `Valid.stored.guardLoad` (`Schema.lean:113-116`), and is unreachable on well-formed states (LAPI-07).

## Acceptance criteria

- The three unique indexes are `unique` declarations; `Unique PlayerRow`, `Unique TokenRow` and `Unique ReceiptRow` each have exactly one constructor, with key types `String`, `String` and `(Ref PlayerRow × String × String)`.
- `InsertError GameRow`'s `duplicate` case cannot be built, because `Unique GameRow` is empty (`GameRow` declares no unique index). A test pins it: a `match` on `InsertError GameRow` that omits `duplicate` compiles.
- `Checked GameRow` values for `openGame`, `playMove` and `resign` are built from the domain proofs; `Valid.check` is not called on those paths.
- The schema fingerprint is unchanged, or the migration is recorded. The DDL of the unique indexes must be identical.

## Tests

- **A duplicate player name** is refused by LeanDB with `.duplicate .byName holder`, where `holder` is the existing player's id.
- **A token for a missing player** is refused with `.missingRef .player`.

## Compatibility

The DDL must stay identical, so existing databases open without migration. If index names change (`uq_…`), record a migration.

## Status (2026-09-23)

Done against LeanDB M14 part A (`64c768e`, pinned by commit), branch `lapi-04-typed-schema`.

- Criteria 1, 3 and the two tests are met. `Checked GameRow` is built from proofs (`GameRow.checked`/`checkedOpen`/`checkedStep`), and `Valid.check` is no longer called by the repository. LeanDB's LDB-16 invariant (proved equal to `Valid`, `GameRow.invariant_iff`) now does the check that `guardLoad`/`guardWrite` used to do.
- Criterion 2: `InsertError` is M14b, so the "`match` without `duplicate`" pin waits for it. `Unique GameRow` is pinned empty (`tests/Tests/Games.lean`), and that is the fact that pin would rest on.
- Criterion 4: the DDL is **not** identical. `unique%` names indexes `uq_<table>_<ctor>`, and the declared invariant is part of the fingerprint. The migration is recorded: `Runtime.open` migrates a v1 instance (three index renames and an invariant restamp, non-destructive), and a test opens a real v1 file.
