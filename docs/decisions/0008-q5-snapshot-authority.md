# 0008. Snapshots, revisions, and when authority is checked (Q5)

Status: accepted (provisional), M4, 2026-09-22.

## Decision

- **Reads** run on read-only connections (WAL mode), each inside a LeanDB
  deferred transaction. A single read sees one snapshot. The visibility policy
  is part of the SQL predicate (`x = actor OR o = actor`), and the decoded row
  is re-checked with the Lean `visible` predicate.
  A list's count and page are one logical read and share one deferred
  transaction, including when another connection commits between statements.
- **Writes** go through one writer thread and one connection. Each command's
  commit is one `BEGIN IMMEDIATE` transaction that:
  1. replays or refuses a keyed command whose receipt already exists,
  2. re-loads the target game **with the policy in the query**, and refuses
     unless it equals the game the decision was made against (same revision,
     same participants, same moves),
  3. writes with LeanDB `update` (compare-and-swap on every column, `rev`
     included),
  4. inserts the receipt.
- **Authority is checked twice**: at admission, against the snapshot the
  decision used, and at commit, against the row being replaced, under the write
  lock. If participation was revoked in between, the commit is refused as
  not-found. If the game moved on, the commit is refused as a conflict (412).
  The observable outcome is as if the command ran at the commit instant.
- Sessions (token rows) are checked at admission only. Deleting a token does
  not abort a command that was already admitted. The request timeout bounds
  how long the client waits, but cancellation is cooperative and does not
  guarantee that an admitted command cannot commit after a 504 response.
  Callers must treat a timeout's write outcome as unknown and retry with an
  idempotency key when they need a definitive result.

## Consequences

- Sequential reasoning suffices for the proofs (M6): the model's `step`
  processes one request at a time, and the native commit's lock + CAS makes
  concurrent commands serializable per game. This last step is **checked**
  (tests: 8 simultaneous moves → exactly 1 commit; the same key submitted
  concurrently → one transition), not proved.
- Cross-game invariants are out of scope for this slice.
