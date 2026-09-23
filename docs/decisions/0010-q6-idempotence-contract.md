# 0010. The idempotence contract (Q6)

Status: accepted (provisional), M6, 2026-09-22.

## Contract

- **Key scope:** `(actor, operation, Idempotency-Key)`. Keys of different
  actors or operations never interact.
- **Input identity:** a SHA-256 fingerprint of the *canonical decoded input*
  (e.g. `playMove|<game>|<rev>|<cell>`), not of the raw bytes. Reformatted
  JSON is the same request. A different input under the same key is refused
  with 422 and changes nothing.
- **What is recorded:** the full response (status, headers, body), in the same
  transaction as the state change. A failed or refused command records
  nothing, so it can be retried with the same key.
- **Replay:** the recorded response, marked `Idempotent-Replayed: true`. The
  world is unchanged.
- **Retention:** receipts are kept indefinitely in this slice. Expiry is a
  later change and weakens the theorem to "within retention".
- **Replay under revoked authority:** replay is by the recording actor only
  (key scope), and returns what that actor was already told. It reveals
  nothing new, so a replay is served even if the actor has since lost access
  to the game. (Chosen deliberately: it keeps retries safe across revocation.)
- **Concurrent submissions:** the single writer serializes commits. The
  second transaction sees the first one's receipt and replays it (checked by
  tests, not proved).

## Theorems (M6)

- `keyed_replay`: for a routed, authenticated, decoded keyed write with a
  fresh key and a successful first commit, an **immediate** replay returns
  `res` marked as a replay and leaves the world unchanged. Replay after
  intervening requests remains unproved.
- `resign_idem` (domain) and `resign_state_idem` (model): resigning twice
  has the same state effect as once, even without a key.
- `reads_pure`: `GET` routes never change the world.
