<!--
blog-check prelude
import Scheduling.Api
import Scheduling.Bypass
open LeanDb LeanApi Scheduling PolicyView
-->
<!--
Every ```lean block is checked by scripts/check_blog.sh. Everything shown
exists in this tree. Theorems are about pure domain functions, not DbState.
-->

# A calendar that can't double-book, and only says when you're busy

Two people must not occupy the same 30 minutes on one host's calendar. Anyone looking at that host should see busy intervals, not the meeting title, the notes, or who is coming. Those two rules are the product. They fail, in ordinary backends, in the gaps between the API, the handler, the query and the database: a unique index without a typed clash, a list endpoint that forgets to drop a column, a 403 that admits the booking exists.

This post is a small Calendly-style service on LeanAPI and LeanDB. Each guarantee is either a theorem about a pure function, a compile error, a named test, or something still planned. Nothing about the running database is called a proof: at the pinned LeanDB, `DbState` is empty inside a proof.

## How this usually goes wrong

A typical stack encodes "one booking per slot" as a unique index *and* as a `SELECT … FOR UPDATE` *and* as an `if booked` in the handler. Under retries and concurrent posts, the three disagree. The conflict might be a 500, or a 200 that overwrote the first invitee.

Free/busy is often "load the bookings and drop fields in the serializer." One intern adds `invitee` to the JSON "for debugging." The query still selected it. A status code can leak too: 403 on someone else's booking, 404 on a missing id.

The point of this example is to be honest about which layer enforces each rule, and to tie the policy and the projection to the domain by proof. `rule` and the SQL `scope` are still written twice; that match is planned, not proved.

## The example on one screen

Three tables. People, published openings, and bookings. The no-double-booking rule is a unique index on the booking:

<!-- check: excerpt examples/scheduling/Scheduling/Schema.lean -->
```lean
unique% PersonRow.byHandle := handle
unique% PersonRow.byDigest := digest
unique% AvailabilityRow.bySlot := (host, slot)
unique% BookingRow.bySlot := (host, slot)

schema% Calendar := PersonRow, AvailabilityRow, BookingRow
```

`BookingRow` stores host and invitee on the row, so the access rule is single-table (the current LeanDB envelope: no child-list filters, no `Option (Ref _)`).

Who may see a booking's details is a policy. Its `rule` is proved equal to the domain's `visibleTo` through the row mapping for rows whose person ids are non-negative, which covers every id LeanDB issues (`bookingPolicy_rule_eq_visibleTo`). With no condition at all, a row the policy admits is visible in the domain (`bookingPolicy_rule_implies_visibleTo`). The SQL `scope` is the same predicate written again:

<!-- check: excerpt examples/scheduling/Scheduling/Policies.lean -->
```lean
instance : Policy Calendar PersonId BookingRow where
  rule p r := r.val.host == pref p || r.val.invitee == pref p
  scope p := (LeanDb.Query.from BookingRow).where' fun r =>
    r.val.host == pref p || r.val.invitee == pref p
```

Those two fields are not a theorem. `policy%` would generate both from one lambda; until then, `scope` matching `rule` is planned. What *is* proved is that `rule` is `visibleTo` of the reconstructed booking, on the non-negative foreign keys LeanDB issues:

<!-- check: signature Scheduling.bookingPolicy_rule_eq_visibleTo -->
```lean
theorem bookingPolicy_rule_eq_visibleTo (p : PersonId) (s : Stored BookingRow)
    (hh : 0 ≤ s.val.host.toInt64) (hi : 0 ≤ s.val.invitee.toInt64) :
    Policy.rule (s := Calendar) p s = Booking.visibleTo p (reconstruct s)
```

`writePolicy_admits_ofBooking` is the same kind of fact for inserts: `admits` on `ofBooking b` is `p == b.invitee`. A table with no instance cannot be read through the view. `PersonRow` has none — default deny for token digests.

The public endpoint does not return a booking. Its type is a list of intervals, built as a projection:

<!-- check: excerpt examples/scheduling/Scheduling/Api.lean -->
```lean
def listBusy (host : Path PersonId) : Read Calendar BusyCalendar := do
  let busy ← ProjRead.toRead (ProjRead.busy host.val)
  pure { host := host.val.n, busy := busy.map BusyIntervalView.of }
```

`Read Calendar` means it cannot write. There is no `Auth`: anyone may call it. `ProjRead.busy` maps each stored booking to `BusyInterval` (start and finish only). The SQL filter for host 1 is:

```text
WHERE t0."host" IS ?
params [INTEGER 1]
```

LeanDB still selects the entity. The hidden columns are not in the handler's type; they are still on the wire from SQLite. Column-restricted `SELECT` is planned.

Booking is a transaction. The signature is the spec:

<!-- check: signature Scheduling.book -->
```lean
def book (me : Auth PersonId) (host : Path PersonId) (body : Body BookBody) (now : Now) :
    Tx Calendar ScheduleError (Created BookingView)
```

The caller is an authenticated person. The host id is in the path. The body is a `Slot` (aligned Unix seconds), a `Title` and `Notes` — not strings the handler re-parses. `Now` is the request time. The effect is `Tx`: one `BEGIN IMMEDIATE`, commit or roll back. Success is 201 with the booking. Failure is a case of `ScheduleError`.

The five routes:

<!-- check: excerpt examples/scheduling/Scheduling/Api.lean -->
```lean
def calendarApi : DbApi Calendar := api! [
  .get    "/hosts/{id:nat}/busy"         listBusy,
  .post   "/hosts/{id:nat}/availability" publish,
  .post   "/hosts/{id:nat}/bookings"     book,
  .get    "/bookings/{id:nat}"           readBooking,
  .delete "/bookings/{id:nat}"           cancelBooking
]
```

## How each headline is enforced

### 1. No double booking

The unique index is the concurrent rule. The insert handles the only clash that can happen:

<!-- check: excerpt examples/scheduling/Scheduling/Api.lean -->
```lean
        | some (.error (.duplicate .bySlot _)) => TxnAs.throw .taken
        | some (.error (.missingRef _)) => TxnAs.throw .missingPerson
```

`.taken` is 409, `"that slot is already booked"`. There is no other unique index on `BookingRow`. Adding one makes this `match` stop compiling. `nomatch` on `.bySlot` is refused too.

A sequential check, `decideBook`, also refuses a taken slot. That is not what saves you under two concurrent POSTs. The test `exactly one concurrent booking wins` fires eight requests at the same opening: one 201, seven 409.

Aligned slots with different starts never overlap, as a fact about the domain:

<!-- check: signature Scheduling.aligned_slots_disjoint -->
```lean
theorem aligned_slots_disjoint (a b : Slot) (h : a.start ≠ b.start) :
    Interval.overlaps a.interval b.interval = false
```

So "book a start" is enough. You do not also have to prove interval geometry in the handler.

### 2. Free/busy reveals only busy intervals

The projection type holds Unix start and finish. Changing titles, notes or invitees does not change it:

<!-- check: signature Scheduling.retitle_preserves_freeBusy -->
```lean
theorem retitle_preserves_freeBusy (bs : List Booking) (t : Title) :
    freeBusy (bs.map (retitle · t)) = freeBusy bs
```

The same holds for `renote_preserves_freeBusy` and `reinvite_preserves_freeBusy`. `listBusy` does not call `freeBusy` by name. It maps `Project` over the rows the query yields. That map *is* `freeBusy` of the reconstructed bookings:

<!-- check: signature Scheduling.project_list_eq_freeBusy -->
```lean
theorem project_list_eq_freeBusy (rows : List (Stored BookingRow)) :
    rows.map (Project.project (α := BookingRow)) = freeBusy (rows.map reconstruct)
```

So those noninterference theorems describe what the endpoint returns, given the rows the query yields. They do not describe which rows the query yields.

A real response after booking `"secret intro"`:

```http
GET /hosts/1/busy
{"busy":[{"finish":2000001600,"start":1999999800}],"host":1}
```

The test `free/busy does not contain the title` checks the body. A stranger still cannot read `/bookings/1` (404 if they are logged in as someone else, 401 if they send no token).

### 3. Only the host or the invitee can read details or cancel

`readBooking` runs over `ReadAs`: the policy and the id go to SQL together. Cancel uses `TxnAs.deleteVisible`: no row in the view, no delete. After a 204, the unique slot is free. The pure version of that fact:

<!-- check: signature Scheduling.cancel_frees -->
```lean
theorem cancel_frees (bs : List Booking) (b : Booking)
    (huniq : ∀ b' ∈ bs, b'.id = b.id ∨ b.host ≠ b'.host ∨ b.slot ≠ b'.slot) :
    occupied (cancel bs b.id) b.host b.slot = false
```

The test `cancel frees the slot` then books the same start again and gets 201.

### 4. In the future, and inside published availability

`Slot` only constructs if `start` is aligned to 30 minutes and the finish fits below 2^63. Unaligned JSON is 422 at the boundary, before the handler:

```http
POST /hosts/1/availability  {"start":1999999801}
{"detail":"request validation failed","errors":[{"loc":"body.start","msg":"slot must be aligned to 30 minutes UTC"}],"status":422,...}
```

`decidePublish` and `decideBook` take `Now`. A successful book is in the future and on a published slot (`decideBook_future`, `decideBook_available`). The unique index, not `decideBook`, is what two overlapping requests hit.

## What a mistake looks like

A `GET` whose handler is a transaction does not build. Verbatim from the `#guard_msgs` pin in `tests/Tests/Scheduling.lean`:

```text
error: could not synthesize default value for parameter 'safe' using tactics
---
error: a GET or HEAD endpoint must not change state, but this handler's effect is `writes`. Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.
```

Smuggling a full booking row into the free/busy program:

<!-- check: excerpt examples/scheduling/Scheduling/Bypass.lean -->
```lean
def sneakyBusy (host : PersonId) : ProjRead Calendar (Stored BookingRow) :=
  ⟨Read.all (BookingRow.busyOf host)⟩
```

```text
error: Invalid `⟨...⟩` notation: Constructor for `Scheduling.ProjRead` is marked as private
```

Pretending the unique index cannot clash:

```text
error: Missing cases:
BookingRow.Unique.bySlot
```

That last one is the "add an index and this stops compiling" story, in reverse: the index is there, so you must name `.bySlot`.

## What exactly is guaranteed

### Proved

About pure functions, not `DbState`:

- `aligned_slots_disjoint` — distinct aligned starts do not overlap
- `next_aligned_le` — the arithmetic that lemma uses
- `freeBusy_congr`, `retitle_preserves_freeBusy`, `renote_preserves_freeBusy`, `reinvite_preserves_freeBusy` — free/busy depends only on intervals
- `project_eq_toBusy`, `project_list_eq_freeBusy` — mapping `Project` over stored rows is `freeBusy` of the reconstructed bookings
- `bookingPolicy_rule_eq_visibleTo` — on non-negative foreign keys, the booking `rule` is `visibleTo` of `reconstruct`
- `bookingPolicy_rule_implies_visibleTo` — if the policy admits you, `visibleTo` holds (no extra hypothesis)
- `writePolicy_admits_ofBooking` — `WritePolicy.admits` on `ofBooking b` is `p == b.invitee`
- `writePolicy_admits_eq_invitee`, `ref_beq_pref`, `pref_inj`, `pid_pref`
- `cancel_frees` — under unique `(host, slot)`, cancel frees the slot
- `decideBook_ok`, `decideBook_future`, `decideBook_available` — an accepted book is in the future and published
- `decidePublish_future`
- `visibleTo_host`, `visibleTo_invitee`
- codec round-trips: `instant_roundtrip`, `slot_roundtrip`, `nat_roundtrip`

### Enforced by the types

- `GET` cannot use `publish` or `book` (`#guard_msgs` on `.get … publish`)
- `ProjRead` / `ReadAs` / `TxnAs` constructors are private (`sneakyBusy`, `sneakyRead`, `sneakyWrite`)
- `Actor` cannot be forged (`spoof`)
- no `Policy` for `PersonRow` (`sneakyPeople`)
- `InsertError BookingRow` must handle `.duplicate .bySlot`; `nomatch` on that index is refused
- `Slot`, `Title`, `PersonId` are smart constructors shared by HTTP and columns; unaligned starts never reach `book`

### Tested

In `tests/Tests/Scheduling.lean`, sections `scheduling: seed and free/busy projection` and `scheduling: concurrent double-book`:

- `bob books 201`, `double book 409`
- `exactly one concurrent booking wins`, `the rest are 409 taken`
- `free/busy does not contain the title`, `free/busy does not contain notes`
- `stranger cannot read details`, `missing and hidden are the same 404`
- `bob cancels 204`, `cancel frees the slot`
- `unaligned start 422`, `past slot 422`, `bob cannot publish alice's slots`

### Planned

These are DESIGN.md §7.5. They need LeanDB M15 (`DbState` with real content, meaning = SQL):

- Restricted reads: a program over the view observes only admitted rows
- Frame: two states that agree on the view (and the declared releases) give the same result
- Write confinement: a transaction does not change rows the actor cannot see
- Noninterference for every route of `calendarApi`, from the database layer, not a proof per endpoint
- Coverage: `api!` refuses a handler whose program is over the unscoped schema
- Pushing `Project` into `SELECT` so titles are not fetched for free/busy
- That `scope` equals `rule` (needs `policy%`, or LeanDB's view laws)

Until then, isolation of the running service is tested, not proved. The type checker already refuses the bypasses above. The policy–domain and projection–`freeBusy` lemmas above are about the functions, given a row list, not about which rows SQL returns.
