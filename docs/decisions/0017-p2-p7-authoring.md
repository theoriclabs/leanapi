# 0017. Proof automation vs explicit obligations (P2), app properties (P6), runtime checks (P7)

Status: accepted (provisional), M9, 2026-09-23. Settles [PROPERTIES.md](../PROPERTIES.md) P2, P6 and P7.

## P2: what is automated, and what the author sees

- `preserves I by f₁, …` generates one theorem per decision function,
  `I.preserved_f : I s → f … s = .ok s' → I s'`. A function with no
  argument of the carrier type is a constructor, and its obligation has no
  `I s` premise.
- `invariant_cases` does the routine part: unfold the decision, split every
  `if`/`match`, close refusal branches, split `I` into its fields, then per
  field try the frame (`hI.field`), `simp_all` (with the author's lemmas and
  the fields of `hI` in context), `omega`, `decide`.
- Anything left stays **visible**: the command fails and prints each goal,
  tagged by branch and field, with the branch conditions named `c1, c2, …`.
  The author adds `| f => tactic` for exactly those goals. There is no
  silent fallback and no `sorry`: a proof that uses `sorry` is refused.
- Generated code is plain: the structure, `fields`, `holdsB`, `check`,
  `holdsB_iff`, `check_iff` and the `Decidable` instance are ordinary
  declarations a user could write by hand.

private-games: `openGame` is fully automatic (with `Game.opened`,
`Rules.legalHistory` as lemmas). `playMove` needs 4 one-line field cases
(`nodup`, `history`, `length`, `rev`), and `resign` needs 2 (`rev`,
`resignedBy`). The hand-written `validB`, `resignedOk` and `validB_iff`
(20 lines) are gone.

## P6: app-specific properties use the same machinery

Yes. `Valid` is declared with the same `invariant` command a library
property would use, registered in the same registry, and lifted to the
store by the same `ListStore` lemmas. The cost is small: an invariant is a
structure of fields.

## P7: the runtime check is generated from the proved definition

`invariant` generates `check`, and `StoredInvariant` packages it with the
proof that passing the check establishes the property (`guardWrite_ok`,
`guardLoad_ok`). The private-games repository calls
`Valid.stored.guardLoad` on every load and `Valid.stored.guardWrite` before
every write. The error names the failing fields.

LeanDB 0.4.0 has no per-entity invariant hook (`@[leandb_invariant]` was a
sketch in PROPERTIES.md), so the adapter is called from the repository
inside the write transaction. If LeanDB adds a hook, `StoredInvariant.check`
is what to register.

A field marked `proof_only` is proved but not checked at runtime. Then only
the sound direction (`check_of`: the property implies the check passes)
is generated, and there is no `StoredInvariant` from `check_iff`, so the
weaker runtime check cannot be mistaken for the property.
