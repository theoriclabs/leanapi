<!--
blog-check prelude
import Helpdesk.Domain
import Helpdesk.Schema
import Helpdesk.Policies
import Helpdesk.Api
open Helpdesk LeanDb LeanApi PolicyView
-->
<!--
Every `lean` block is checked by `scripts/check_blog.sh`. Claims about the
running service are type-checked or tested, never proved: at the pinned
LeanDB, `DbState` is empty in proofs (review H1).
-->

# A help desk that cannot leak an internal note

Support software has a rule that is easy to state and easy to get wrong:
**customers never see an agent's internal note**, and **nobody ever reads
another tenant's tickets**. The same tables serve both kinds of user. A
forgotten `WHERE`, a serializer that includes every column, or a webhook
retry that opens a second ticket, and the rule is gone.

This post is a small LeanAPI backend for that rule: two orgs, agents and
customers, five HTTP endpoints. The rule is written as a domain function
(`seesMessage`, `seesTicket`) and as a policy (`rule` and `scope`). A
lemma proves that `rule` implies the domain function on a reconstructed
row. That the SQL `scope` matches `rule` is **not** proved: that needs
`policy%` (one lambda generating both) or LeanDB's view laws. What
follows is what is actually guaranteed today, and what still waits on
LeanDB.

## How ordinary backends lose the rule

The usual shape is a handler that loads a ticket, then a second query for
its messages, then a filter in application code: drop rows where
`internal = true` if the caller is a customer. That filter lives in one
place. A list endpoint, an export, a search indexer, or a "include
everything" admin path does not call it.

Tenant isolation is the same story with `org_id`. Miss it on one query and
a customer of Globex reads Acme. The 404 for "not yours" is often a
different body from "does not exist", so ids leak even when the payload is
hidden.

Inbound email makes a fourth hole. Providers retry. Without a unique key
on `(org, Message-ID)`, the same message becomes two tickets.

None of this is exotic. It is the gap between the rule you meant and the
queries you shipped.

## The example, on one screen

A principal is a user, an org, and a role. Tickets and messages carry the
fields the policy needs on the row itself, so every policy stays
single-table (LeanDB cannot yet filter on child lists).

The customer's view of a message:

<!-- check: excerpt examples/helpdesk/Helpdesk/Domain.lean -->
```lean
def seesMessage (who : Who) (m : Message) : Bool :=
  decide (who.org = m.org) &&
    match who.role with
    | .agent => true
    | .customer => decide (who.user = m.requester) && !m.internal
```

Read: same org; agents see every message in that org; a customer sees only
messages on their own tickets, and only if `internal` is false.

The policy is a second copy, on stored rows. `rule` is what the lemmas
talk about; `scope` is what LeanDB compiles to SQL. They are written by
hand. `message_rule_implies_seesMessage` says a row `rule` admits
reconstructs to a message `seesMessage` allows. A stored `Ref` that
compares equal to `oref o` reconstructs to `o`; the converse can fail
for a negative id, so this is an implication, not an equality.

<!-- check: excerpt examples/helpdesk/Helpdesk/Policies.lean -->
```lean
instance : Policy HelpdeskDb Who MessageRow where
  rule who m :=
    m.val.org == oref who.org &&
      (who.role == Role.agent ||
        (m.val.requester == uref who.user && m.val.internal == false))
  scope who :=
    (Query.from MessageRow).where' fun m =>
      m.val.org == oref who.org &&
        (who.role == Role.agent ||
          (m.val.requester == uref who.user && m.val.internal == false))
```

<!-- check: signature Helpdesk.message_rule_implies_seesMessage -->
```lean
theorem message_rule_implies_seesMessage (who : Who) (m : Stored MessageRow)
    (h : Policy.rule (s := HelpdeskDb) (P := Who) (α := MessageRow) who m = true) :
    seesMessage who (reconstructMessage m) = true
```

An endpoint does not re-state that. It reads through the view. Its type
is the spec: who may call it, that it only reads, and that a miss is
`HelpError`.

<!-- check: signature Helpdesk.readTicket -->
```lean
def readTicket (me : Auth Who) (id : Path TicketId) :
    Read HelpdeskDb (Except HelpError TicketDetail)
```

`Auth Who` is the caller the framework established. `Path TicketId` is a
bounded id, not a string. `Read` cannot write. `HelpError.hidden` is a 404
with no detail: another org, another customer's ticket, and a missing id
are the same response.

## Four headline guarantees

### 1. Tenant isolation

`seesTicket` / `seesMessage` require `who.org = row.org`. The theorems
`other_org_invisible_ticket` and `other_org_invisible_message` say that
of the pure functions. The running service applies the SQL scope:

```text
customer GET ticket 1:
  ((t0."org" IS ? AND t0."requester" IS ?) AND t0."id" IS ?)
agent GET ticket 1:
  (t0."org" IS ? AND t0."id" IS ?)
```

Lean folds the role test into the query: a customer is never an agent, so
the requester conjunct stays; an agent does not need it. Globex listing
Acme's ticket, or guessing its id, is a 404 identical to a missing row
(test `helpdesk tenant isolation`).

```http
GET /tickets/1
Authorization: Bearer gwen

HTTP/1.1 404 Not Found
Content-Type: application/problem+json

{"status":404,"title":"Not Found","type":"about:blank"}
```

Gwen is an agent at Globex. Ticket 1 is Acme's. Gina, a Globex customer,
lists `[]` until someone opens a ticket for her (test `gina lists 0 before
globex inbound`).

### 2. Customers never see an internal note

The customer's thread is `threadFor`: `seesMessage` applied to the list.
That function contains no internal note, nothing from another org, and
nothing whose requester is someone else:

<!-- check: signature Helpdesk.customer_thread_no_internal -->
```lean
theorem customer_thread_no_internal (who : Who) (ms : List Message)
    (hr : who.role = .customer) :
    ∀ m ∈ threadFor who ms, m.internal = false
```

Also `customer_thread_same_org` and `customer_thread_own`. These are proofs
about a list filter, not about SQLite.

At run time the message policy's SQL never fetches `internal = true` for a
customer. Ada posts a note; Carl's GET of the same ticket omits it; Ada's
includes it (test `helpdesk internal notes`):

```http
GET /tickets/1
Authorization: Bearer carl

HTTP/1.1 200 OK
Content-Type: application/json

{"messages":[{"author":1,"body":"I cannot sign in.","createdAt":1790235599,"id":1,"internal":false}],"ticket":{"id":1,"openedAt":1790235599,"requester":2,"status":"open","subject":"Login broken"}}
```

Ada's body on the same GET has two messages; the second has
`"internal":true`.

A customer cannot *write* an internal note either. `mayPost` is false, and
the write view refuses a row the policy would not admit:

<!-- check: signature Helpdesk.customer_never_posts_internal -->
```lean
theorem customer_never_posts_internal (who : Who) (t : Ticket)
    (hr : who.role = .customer) : mayPost who t true = false
```

<!-- check: excerpt examples/helpdesk/Helpdesk/Policies.lean -->
```lean
instance : WritePolicy HelpdeskDb Who MessageRow where
  admit who m :=
    m.org == oref who.org && m.author == uref who.user &&
      (who.role == Role.agent ||
        (m.requester == uref who.user && m.internal == false && who.role == Role.customer))
```

Carl posting `"internal":true` is 403 (test `customer internal 403`). A
customer-authored internal row also fails the table invariant, so it cannot
be stored even if a handler forgot the check:

<!-- check: excerpt examples/helpdesk/Helpdesk/Schema.lean -->
```lean
@[leandb_invariant]
def MessageRow.invariant (r : MessageRow) : Bool :=
  Bool.not (decide (r.authorRole = .customer) && r.internal)
```

`MessageRow.invariant_iff` ties that flag to `Message.ok`. Inserts of
customer replies go through `MessageRow.checkedCustomer`, whose proof is
`draft_customer_ok`.

### 3. Who may write

Only agents write internal notes; customers reply only on their own open
tickets; nobody writes to a closed ticket.

The handler reads the ticket through `TxAs.get` (the read policy), then
asks `mayPost`. Closed is a domain fact about the ticket, not a column on
the message, so the write policy cannot see it without a join. The tests
are `helpdesk who may write`: Gina posting on Acme's ticket is 404; Carl
cannot advance; three advances reach `closed`; the fourth is 409; a reply
on a closed ticket is 409.

<!-- check: signature Helpdesk.closed_is_final -->
```lean
theorem closed_is_final : nextStatus .closed = none
```

`advance_not_from_closed`, `closed_ticket_nobody_posts`, and
`customer_never_advances` are the rest of that lifecycle, as pure
functions.

### 4. Exactly once

Email providers retry. The unique index is per tenant:

<!-- check: excerpt examples/helpdesk/Helpdesk/Schema.lean -->
```lean
unique% TicketRow.byInbound := (org, inboundId)
```

The inbound endpoint (agents only) looks up `(org, Message-ID)`, then
`insert?`. A duplicate looks up again and returns the existing ticket as
200, not 201. The same Message-ID at Globex is a different row (test
`helpdesk inbound exactly-once`):

```http
POST /inbound
Authorization: Bearer ada
Content-Type: application/json

{"messageId":"<m1@acme>","requester":2,"subject":"Login broken","body":"I cannot sign in."}

HTTP/1.1 201 Created
Location: /tickets/1

{"id":1,"openedAt":1790235599,"requester":2,"status":"open","subject":"Login broken"}
```

The retry is `HTTP/1.1 200 OK` with the same body and no `Location`.

## What a mistake looks like

A GET that posts a message does not build. The compiler's words, from
`#guard_msgs` in `tests/Tests/Helpdesk.lean`:

```text
error: a GET or HEAD endpoint must not change state, but this handler's effect is `writes`. Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.
```

Smuggling an unscoped `Read.get` into the view:

```text
error: Invalid `⟨...⟩` notation: Constructor for `PolicyView.ReadAs` is marked as private
```

Reading `OrgRow` (no `Policy` instance, default deny):

```text
error: failed to synthesize instance of type class
  Policy HelpdeskDb Who OrgRow
```

`TxAs.mk` is private too: an unscoped `Txn` cannot be put in the write
view (`#guard_msgs` `sneakyWrite` in the test file). `Actor.mk` is private
in PolicyView, so a program cannot act as someone else that way. `Auth`'s
constructor is still public in the framework; that is the same caveat
PolicyView documents, not a help-desk proof.

<!-- check: compile -->
```lean
example (who : Who) (m : Message) (hr : who.role = .customer)
    (h : seesMessage who m = true) : m.internal = false :=
  customer_never_sees_internal who m hr h
```

That last block is the domain lemma. `message_rule_implies_seesMessage`
says a row the policy's `rule` admits reconstructs to a message that
lemma allows. Matching `scope` to `rule` is still planned. Neither
mentions `DbState`.

## What exactly is guaranteed

### Proved

Theorems about pure domain functions, the row mapping, and codecs, in
`Helpdesk/Domain.lean`, `Helpdesk/Schema.lean`, and `Helpdesk/Policies.lean`:

- Visibility: `seesTicket_same_org`, `seesMessage_same_org`,
  `customer_sees_own_ticket`, `customer_never_sees_internal`,
  `customer_sees_own_message`, `customer_thread_no_internal`,
  `customer_thread_same_org`, `customer_thread_own`,
  `other_org_invisible_ticket`, `other_org_invisible_message`.
- Policy `rule` vs domain (implications: a stored `Ref` that `== oref o`
  reconstructs to `o`; the converse can fail for a negative id):
  `ticket_rule_implies_seesTicket`, `message_rule_implies_seesMessage`.
- Write policy vs domain: `ticket_admit_implies_agent`,
  `ticket_admit_implies_seesTicket`, `message_admit_implies_seesMessage`;
  on a row mapped from the domain, `mayAdvance_implies_ticket_admit`,
  `mayPost_implies_message_admit`. `admit` does not include "not closed".
- Writes: `mayPost_implies_sees`, `mayPost_same_org`, `mayPost_not_closed`,
  `customer_never_posts_internal`, `closed_ticket_nobody_posts`,
  `mayAdvance_agent`, `mayAdvance_not_closed`, `customer_never_advances`.
- Lifecycle: `closed_is_final`, `nextStatus_some_not_closed`,
  `advance_refuses_closed`, `advance_not_from_closed`, `openFromEmail_open`.
- Invariant and drafts: `Message.ok` via `draft_customer_ok`,
  `draft_agent_ok`; `MessageRow.invariant_iff`, `MessageRow.Invariant_iff`,
  `MessageRow.ofMessage_invariant`.
- Codecs: `nat_roundtrip`, `instant_roundtrip`, `Instant.make_unix`,
  `oid_oref`, `uid_uref`, `tid_tref`, `beq_oref_implies_oid`,
  `beq_uref_implies_uid`.

None of these quantify over `DbState`, `Read.denote`, or `Txn.denote`.

### Enforced by the types

The compiler refuses:

- a GET or HEAD whose handler writes (`#guard_msgs` in
  `tests/Tests/Helpdesk.lean`);
- an unscoped `Read` inside `ReadAs`, a forged `Actor`, a read of `OrgRow`
  (`#guard_msgs` in `Helpdesk/Policies.lean`);
- an unscoped `Txn` inside `TxAs` (`sneakyWrite`);
- a `Checked MessageRow` that fails `Message.ok` (customer internal notes
  have no `checkedCustomer` path).

Ids, subjects, bodies, and timestamps go through smart constructors shared
by HTTP and storage. A wrapped ticket id is 422, not a silent `Nat`.

### Tested

`Tests.HelpdeskHttp.run` in `tests/Tests/Helpdesk.lean`, against SQLite:

- `helpdesk auth` — missing or unknown bearer is 401.
- `helpdesk inbound exactly-once` — retry 200, same id; same Message-ID in
  another org is a different ticket.
- `helpdesk tenant isolation` — other org ≡ missing (status and body);
  Gina does not see Acme's ticket.
- `helpdesk internal notes` — agent sees `internal: true`; Carl does not;
  customer internal post is 403.
- `helpdesk who may write` — cross-tenant post 404; customer cannot
  advance; closed is 409 for advance and reply.
- `helpdesk policy SQL` — customer GET binds org, requester, and id;
  agent GET binds org and id.

### Planned

DESIGN.md §7.5, which need LeanDB M15 (`DbState` with real content in
proofs, execution agreeing with meaning):

- **Restricted reads** — a program over `S.As p` observes only rows `p`'s
  policy admits.
- **Frame** — two states that agree on `p`'s admitted rows give the same
  result.
- **Write confinement** — a transaction over `S.As p` leaves unadmitted
  rows unchanged.
- **Noninterference for every route** — an API whose authenticated
  programs are all over `S.As me` is noninterfering for
  `SameView p`.
- **Coverage** — `api!` refuses an endpoint over the unscoped schema
  unless it is marked trusted, so reachable and proved are the same routes.
- **`scope` = `rule`** — a `policy%` command that generates both from one
  lambda, or LeanDB view laws that the SQL is the policy. Today they are
  written twice.

Until M15, the `DbState` statements would be vacuous. This example does
not claim them. The running help desk applies `scope` in SQL and the type
of every handler; `rule` is proved to imply the domain function.
