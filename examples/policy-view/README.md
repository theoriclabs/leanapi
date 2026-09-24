# policy-view: row-level policies as a LeanDB view (prototype)

A prototype of [DESIGN.md §7.5](../../DESIGN.md): who may see which rows is declared once per table, and a request's database program can only read through the actor's view. It is built on LeanDB as it is, with no LeanDB changes.

```
lake build PolicyView && lake exe policyview    # writes policy-view-demo.db in the current directory
```

## The pieces

- **`Policy s P α`** (`PolicyView/Policy.lean`): the rule for table `α` and actor type `P`, as a Lean function (`rule`) and as a LeanDB query (`scope`), which LeanDB compiles to SQL. A `policy%` command would generate both from one lambda. In this prototype they are written twice, so keep them identical.
- **`Actor P`**: an authenticated actor. Its constructor is private: application code cannot make one.
- **`ReadAs s me α`**: a read program over the database *as `me` sees it*. Its constructor is private, so the only way to build one is through the scoped operations (`ReadAs.all`, `ReadAs.get`), each of which applies the table's policy in SQL.
- **`ReadAs.forAuth me prog`**: the bridge a `DbApi` handler uses today. It turns a scoped program into the `Read s α` the handler returns, for the request's `Auth` actor.

## What it enforces, at compile time (`PolicyView/Games.lean`, pinned with `#guard_msgs`)

- An unscoped read cannot be put into a view: `⟨Read.get GameRow id⟩` is rejected, because the constructor is private.
- A table with no policy cannot be read: `ReadAs.all TokenRow` fails with "failed to synthesize `Policy Games PlayerId TokenRow`". This is **default deny**.
- A program cannot act as another actor: `⟨⟨2⟩⟩ : Actor PlayerId` is rejected.

## What it does at run time (`PolicyViewMain.lean`)

The policy and the query's own filter go to SQL together, so another actor's rows are never fetched:

```
SQL filter for player 1 asking for game 2:
  WHERE ((t0."x" IS ? OR t0."o" IS ?) AND t0."id" IS ?)   params [1, 1, 2]
player 1 reads game 2: none (404)
player 1 lists: [game 1 (1 vs 2)]
```

## Not yet

- **Writes.** There is no `TxAs`. A scoped write view needs:
  - update and delete only on rows read through the view;
  - new and changed rows admitted by the policy, by proof or by a decided check with a typed failure.
- **Proofs.** The theorems of DESIGN §7.5 (restricted reads, frame, write confinement) need LeanDB M15. At the pinned LeanDB, `DbState` has no content in proofs, so any theorem over `DbState` is vacuous (docs/reviews/2026-09-23-review-lapi-02-05-m14.md, H1).
- **`first`, `page`, `count`.** These need the policy's query to be exact, which `policy%` would check when a policy is declared. The prototype uses `Read.all`.
- **Policies that read other tables** (membership, sharing) are open. Store what a policy needs on the row itself, so every policy is single-table.
