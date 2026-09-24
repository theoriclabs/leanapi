# helpdesk

A multi-tenant help desk on LeanAPI and LeanDB: two orgs, agents and
customers sharing the same tables, and a rule that **a customer never sees
an internal note**. Who may see or change which row is a `Policy` (and a
write view), not a check scattered through handlers.

This is the first example of two kinds of actor on one schema. It builds on
[`examples/policy-view/`](../policy-view/) (`import PolicyView.Policy`; that
prototype is not modified). Proofs are about **pure domain functions**. At
the pinned LeanDB, `DbState` is empty in proofs (review H1), so nothing here
is a theorem about SQLite.

## Run

```bash
lake build helpdesk
./.lake/build/bin/helpdesk --host 127.0.0.1 --port 8080 --db helpdesk.sqlite
```

The first open seeds two orgs and four people. Tokens are demo bearer
strings, not passwords:

| Token | Who |
|---|---|
| `ada` | Ada, agent at Acme |
| `carl` | Carl, customer at Acme |
| `gwen` | Gwen, agent at Globex |
| `gina` | Gina, customer at Globex |

```bash
# Ada opens a ticket from an inbound email (retries keep the same id).
curl -sS -D - -H 'Authorization: Bearer ada' -H 'Content-Type: application/json' \
  -d '{"messageId":"<m1@acme>","requester":2,"subject":"Login broken","body":"I cannot sign in."}' \
  http://127.0.0.1:8080/inbound

# Ada posts an internal note; Carl's GET of the same ticket omits it.
curl -sS -H 'Authorization: Bearer ada' -H 'Content-Type: application/json' \
  -d '{"body":"Reset their password.","internal":true}' \
  http://127.0.0.1:8080/tickets/1/messages
curl -sS -H 'Authorization: Bearer carl' http://127.0.0.1:8080/tickets/1
curl -sS -H 'Authorization: Bearer gwen' http://127.0.0.1:8080/tickets/1
# Gwen (Globex) gets the same 404 as a missing id.
```

## API

| Route | Type (compressed) |
|---|---|
| `GET /tickets` | `Auth Who → Read … (List TicketView)` |
| `GET /tickets/{id}` | `Auth Who → Path TicketId → Read … (Except HelpError TicketDetail)` |
| `POST /tickets/{id}/messages` | `Auth Who → … → Tx … HelpError (Created MessageView)` |
| `POST /tickets/{id}/advance` | agents only; `open → pending → solved → closed` |
| `POST /inbound` | agents only; unique per `(org, Message-ID)` |

`HelpError.hidden` is 404 with no detail (other org, other customer's ticket,
or missing: the same body). `forbidden` is 403; a closed ticket is 409.

A `GET` whose handler is a `Tx` does not compile (`#guard_msgs` in
`tests/Tests/Helpdesk.lean`).

## Layout

| File | What |
|---|---|
| `Helpdesk/Domain.lean` | Ids, `Who`, `Ticket`, `Message`, `seesTicket` / `seesMessage` / `mayPost` / `advanceTicket`, theorems |
| `Helpdesk/Schema.lean` | Four tables, codecs, `MessageRow.invariant`, `Checked` from domain proofs |
| `Helpdesk/Policies.lean` | `Policy` per table, `WritePolicy` + `TxAs`, compile-time refusals |
| `Helpdesk/Api.lean` | Endpoints, `api!`, seed |
| `HelpdeskMain.lean` | HTTP server |

## Design

**Two actors, one pair of tables.** `Who` is a user, an org, and a `Role`
(`agent` or `customer`). Ticket and message policies branch on `role`. There
is no separate agent schema.

**Single-table policies.** Each message stores `org`, `requester` (the
ticket's customer), `authorRole`, and `internal`, so the policy does not
join. This avoids LeanDB D1 (no filter on child-list contents) and the
open question in DESIGN §7.5 about policies that read other tables.

**Read view.** `Policy.rule` is a copy of `seesTicket` / `seesMessage` on
stored rows (`ticket_rule_implies_seesTicket`,
`message_rule_implies_seesMessage`: policy admits ⇒ domain true).
`scope` is a third copy, compiled to SQL, not proved equal to `rule`.
`OrgRow` has no instance: default deny. `ReadAs.get` / `ReadAs.all` are
the only reads. `messagesOn` runs `ReadAs.all` (policy in SQL) and
filters the ticket id in Lean, because `PolicyView.ReadAs` has no
`filter` yet.

**Write view (`WritePolicy` / `TxAs`).** PolicyView has no writes. This
example adds them in the same pattern: private constructor, default deny,
every insert/update decides `WritePolicy.admit`. `TxAs` is indexed by `Who`,
not `Actor`, because `Actor.mk` is module-private in PolicyView. Entry is
`TxAs.forAuth` from the request's `Auth`, whose constructor is private:
only authentication makes one.

**Closed tickets.** `mayPost` / `mayAdvance` are domain checks on the ticket
the view already returned. Status is not a column on the message, so the
write policy cannot see "this ticket is closed" without a join.

**Exactly once.** `unique% TicketRow.byInbound := (org, inboundId)`. The
inbound handler looks up, then `insert?`; a duplicate looks up again. Same
`Message-ID` in another org is a different ticket.

**Invariant.** `MessageRow.invariant` is `Message.ok`: a customer is never
recorded as the author of an internal note. Agent drafts use
`MessageRow.checkedAgent`; customer drafts use `checkedCustomer`, discharged
by `draft_agent_ok` / `draft_customer_ok`.

**Limits avoided (review D1–D10):** no child-list filters, no order by
closed enums, no `Option (Ref _)`, no cascades, no `append`, ids and
instants bounded below 2^63.

## What is guaranteed

**Proved** (pure functions in `Domain.lean` / `Schema.lean` / `Policies.lean`):
`customer_thread_no_internal`, `customer_thread_same_org`,
`customer_thread_own`, `other_org_invisible_{ticket,message}`,
`ticket_rule_implies_seesTicket`, `message_rule_implies_seesMessage`,
`ticket_admit_implies_seesTicket`, `message_admit_implies_seesMessage`,
`mayAdvance_implies_ticket_admit`, `mayPost_implies_message_admit`,
`closed_is_final`, `advance_not_from_closed`, `customer_never_posts_internal`,
`closed_ticket_nobody_posts`, `customer_never_advances`,
`MessageRow.invariant_iff`, codec round-trips.

**Enforced by the types:** unscoped `Read` cannot enter `ReadAs`; `OrgRow`
has no `Policy`; `Actor.mk` and `TxAs.mk` are private; a GET cannot return
`Tx` (`#guard_msgs` in `Policies.lean` and `tests/Tests/Helpdesk.lean`).
`Checked` message rows come from domain proofs.

**Tested** (`Tests.HelpdeskHttp.run`): tenant isolation (including existence
privacy), internal notes, who may write, inbound retries, policy SQL.

**Planned** (DESIGN §7.5, need LeanDB M15): restricted reads, frame, write
confinement, noninterference for every route, coverage (`api!` refuses an
unscoped program). **`scope` = `rule`** needs `policy%` or LeanDB view
laws; they are written twice today. Not claimed of the running service.

The longer write-up is [docs/blog/helpdesk.md](../../docs/blog/helpdesk.md).
