# scheduling: a calendar that can't double-book

A Calendly-style backend on LeanAPI and LeanDB. Hosts publish 30-minute UTC slots. Invitees book them. **Anyone** can see a host's busy intervals. Titles, notes and invitees stay with the host and the invitee.

```bash
lake build scheduling
./.lake/build/bin/scheduling --port 18083 --db calendar.sqlite
# seeds alice (id 1, token alice-token) and bob (id 2, token bob-token)
```

## API

| Route | Who | Notes |
|---|---|---|
| `GET /hosts/{id}/busy` | anyone | busy intervals only |
| `POST /hosts/{id}/availability` `{"start"}` | that host | aligned Unix seconds, in the future |
| `POST /hosts/{id}/bookings` `{"start","title","notes"?}` | an invitee | unique `(host, start)`; 409 if taken |
| `GET /bookings/{id}` | host or invitee | 404 for anyone else, same as missing |
| `DELETE /bookings/{id}` | host or invitee | frees the slot |

`start` is Unix seconds, UTC, aligned to 30 minutes. An unaligned value is 422 at the boundary (`Slot.make`). `Now` is an input; a slot that is not in the future is 422.

## Design

Three tables: `PersonRow` (handle + token digest), `AvailabilityRow` (host, slot), `BookingRow` (host, invitee, slot, title, notes). What a policy needs sits on the row (review D1–D10: no child-list filters, no `Option (Ref _)`, no cascades, Nats below 2^63).

**No double booking** is `unique% BookingRow.bySlot := (host, slot)`. Two concurrent inserts serialize under `BEGIN IMMEDIATE`; the second is `InsertError.duplicate .bySlot`, mapped to 409. That constructor is the only inhabitant of `Unique BookingRow`. Omitting the case, or `nomatch` on it, does not compile (`tests/Tests/Scheduling.lean`).

**Free/busy is a projection**, not a filter in the handler. `ProjRead` (private constructor) returns `List BusyInterval`. Titles, notes and invitees cannot be named in that type. The SQL still `SELECT`s the entity — LeanDB has no column-restricted SELECT yet — and maps in Lean. The handler cannot observe the hidden fields; pushing the projection into SQL is planned with DESIGN.md §7.5.

**Details and cancel** go through `Policy Calendar PersonId BookingRow` (host or invitee) and a write view `TxnAs`: delete only a row already read through the view. `rule` equals `visibleTo` through `reconstruct` (`bookingPolicy_rule_eq_visibleTo`); `WritePolicy.admits` equals “you are the invitee” through `ofBooking`. The SQL `scope` is written again and is not proved to match `rule`. `PersonRow` has no policy: default deny.

Read policies reuse `PolicyView.Policy` (`import PolicyView.Policy`, unchanged). Writes and the projection are in this example: `WritePolicy`, `TxnAs`, `ProjRead`. `Auth`'s constructor is private, so `forAuth` acts for the authenticated caller and no one else.

Proofs are about **pure domain functions** (`aligned_slots_disjoint`, `retitle_preserves_freeBusy`, `cancel_frees`, …). Nothing is claimed as a theorem over the running database: that needs LeanDB M15 (the laws for such proofs, and the check that execution follows the meaning).

## What it guarantees

- **Proved:** aligned slots with distinct starts never overlap; free/busy ignores titles, notes and invitees; mapping `Project` is `freeBusy` of reconstructed rows (`project_list_eq_freeBusy`); the booking `rule` is `visibleTo` through the row mapping; `WritePolicy.admits` is “the actor is the invitee”; cancelling a booking in a list with unique `(host, slot)` frees that slot; a successful `decideBook` is in the future and on a published opening.
- **Enforced by the types:** `GET` cannot return `Tx`; unscoped `Read` cannot enter `ReadAs` or `ProjRead`; `PersonRow` cannot be read through a view; `nomatch` on `BookingRow.Unique.bySlot` is refused. Pinned with `#guard_msgs`.
- **Tested:** double-book 409, including eight concurrent requests with exactly one 201; free/busy body contains no title or notes; stranger 404 on details and cancel; cancel then rebook 201.
- **Planned:** DESIGN §7.5 restricted reads, frame, write confinement, and API-wide noninterference (LeanDB M15). That `scope` equals `rule` (needs `policy%` or LeanDB's view laws). Column-restricted `SELECT` for the projection.

## Curl

```bash
curl -s http://127.0.0.1:18083/hosts/1/busy
curl -s -D - http://127.0.0.1:18083/hosts/1/availability \
  -H "authorization: Bearer alice-token" -H "content-type: application/json" \
  -d '{"start":1999999800}'
curl -s http://127.0.0.1:18083/hosts/1/bookings \
  -H "authorization: Bearer bob-token" -H "content-type: application/json" \
  -d '{"start":1999999800,"title":"secret intro","notes":"private notes"}'
curl -s http://127.0.0.1:18083/hosts/1/busy
# → {"busy":[{"finish":2000001600,"start":1999999800}],"host":1}
#    no title, notes, or invitee
```
