<!--
blog-check prelude
import Billing.Domain
import Billing.Schema
import Billing.Policies
import Billing.Api
open LeanDb LeanApi Billing Billing.Schema Billing.Policies Billing.Api PolicyView
-->
<!--
Every `lean` block below is checked by `scripts/check_blog.sh`:
- `excerpt <file>`: the block appears verbatim in that file;
- `signature <name>`: the block is the exact statement of that declaration;
- `compile`: the block builds on its own.
-->

# Each usage event is counted exactly once

A usage-based SaaS charges for what happened, not for how many times the client said it happened. If a meter retry, a timeout, or a duplicated webhook can add the same event twice, the invoice is wrong. If a tenant can read another tenant's usage, the invoice is also wrong, just in a different way.

This post is a small billing backend in LeanAPI and LeanDB. Four rules are declared once and enforced at the API, in the handler, in the query, and in the stored row. Money is minor units tagged `Currency.usd`; time is UTC unix seconds; ids are not strings. The last section says what is actually guaranteed: proved about pure functions, refused by the type checker, tested against SQLite, or still planned.

## How this usually goes wrong

A worker retries after a network blip and both attempts commit, so the customer is billed twice. An invoice stores a total next to its lines; a later edit updates one and not the other. A `finalized` flag is checked in the happy-path handler and skipped in an admin one. A list query filters by tenant; a get-by-id query forgets to. The rule lived in one function, and another path went around it.

## The example, on one screen

Three tables: tenants (an API key and a unit price in USD cents), usage events, invoices with inline lines. Events are unique on `(tenant, eventId)`. Invoices are unique on `(tenant, year, month)`.

<!-- check: excerpt examples/billing/Billing/Schema.lean -->
```lean
unique% TenantRow.byApiKey := apiKey
unique% UsageEventRow.byTenantEvent := (tenant, eventId)
unique% InvoiceRow.byTenantPeriod := (tenant, year, month)
```

Who may see a row is a `Policy` on that table, default deny, pushed into SQL. The tenant identifier lives on the row itself (LeanDB policies are single-table):

<!-- check: excerpt examples/billing/Billing/Policies.lean -->
```lean
instance : Policy BillingDb Tenant UsageEventRow where
  rule t r := r.val.tenant == tref t.id
  scope t := (LeanDb.Query.from UsageEventRow).where' fun r =>
    r.val.tenant == tref t.id
```

The ingest endpoint's type is the specification. The caller is an authenticated tenant. The body is a typed event, not a bag of strings. The program is a transaction. A duplicate is a replay, not an error.

<!-- check: signature Billing.Api.ingestUsage -->
```lean
def ingestUsage (me : Auth Tenant) (body : Body UsageBody) :
    Tx BillingDb BillingError (Replayed (Created UsageView))
```

A GET of the same handler does not compile: writes are `POST`. The seven routes are one `api!` list.

<!-- check: excerpt examples/billing/Billing/Api.lean -->
```lean
def billingApi : DbApi BillingDb := api! [
  .post "/usage"                       ingestUsage,
  .get  "/usage/{eventId}"             readUsage,
  .post "/invoices"                    createInvoice,
  .get  "/invoices/{id:nat}"           readInvoice,
  .post "/invoices/{id:nat}/finalize"  finalizeInvoice,
  .post "/invoices/{id:nat}/pay"       payInvoice,
  .post "/invoices/{id:nat}/void"      voidInvoiceEp
]
```

Run it with `lake build billing` and `./.lake/build/bin/billing --port 8080 --db billing.sqlite`. Demo keys `acme-live-key` (10¢/unit) and `beta-live-key` (25¢/unit) are seeded on open.

## Counted exactly once

The pure function is idempotent: ingesting the same event twice is ingesting it once.

<!-- check: excerpt examples/billing/Billing/Domain.lean -->
```lean
def ingest (log : List UsageEvent) (e : UsageEvent) : List UsageEvent :=
  if hasEvent log e then log else log ++ [e]
```

<!-- check: signature Billing.ingest_idem -->
```lean
theorem ingest_idem (log : List UsageEvent) (e : UsageEvent) :
    ingest (ingest log e) e = ingest log e
```

Rating follows. `rateLog_append` says quantity × price adds over a concatenation. `rateLog_ingest_idem` says rating a log is unchanged by ingesting an event that is already there. Those are proofs about lists, not about SQLite.

The running service uses the unique index. A second insert of `(tenant, eventId)` is `InsertError.duplicate`. The handler looks the holder up through the tenant's view and answers as a replay:

<!-- check: excerpt examples/billing/Billing/Api.lean -->
```lean
    match ← TxnAs.insert (α := UsageEventRow) (UsageEventRow.checked e) (owns_event me.val e rfl) with
    | .ok _ =>
      pure (.fresh { val := view, location := some loc })
    | .error (.duplicate _ holder) =>
      match ← TxnAs.get UsageEventRow holder with
      | some row =>
        match usageViewOf row.toStored with
        | some v => pure (.replay { val := v, location := some loc })
        | none => TxnAs.throw .hidden
      | none => TxnAs.throw .hidden
```

A real first report, then the same body again:

```http
HTTP/1.1 201 Created
Location: /usage/evt_1

{"eventId":"evt_1","occurredAt":1727136000,"period":{"month":9,"year":2026},"quantity":3}
```

```http
HTTP/1.1 201 Created
Location: /usage/evt_1
Idempotent-Replayed: true

{"eventId":"evt_1","occurredAt":1727136000,"period":{"month":9,"year":2026},"quantity":3}
```

Sending a different quantity under the same id still returns 3 (`same id, other quantity: still first quantity` in `tests/Tests/Billing.lean`). Six concurrent posts of one event are all 201, at least one replay (`concurrent ingest all 201`). That is not a theorem about `DbState`: at this LeanDB pin, table contents are empty inside a proof, so a statement over the database would be vacuous.

## The total is the sum of the lines

An invoice is balanced when the stored total equals the sum of its lines, each line is quantity × unit price, and the line count is bounded.

<!-- check: excerpt examples/billing/Billing/Domain.lean -->
```lean
invariant Balanced (inv : Invoice) where
  total_eq : inv.total.minor = sumAmounts inv.lines
  priced : inv.lines.all (fun l => l.amount.minor == l.quantity.n * l.unitPrice.minor) = true
  bounded : inv.lines.length ≤ maxLines
```

`mkDraft` folds `ingest` over the period's events, rates them, and packs a `DraftInvoice`. The builder comes with a proof:

<!-- check: signature Billing.mkDraft_balanced -->
```lean
theorem mkDraft_balanced {tenant : TenantId} {period : Period} {price : UnitPrice .usd}
    {events : List UsageEvent} {inv : DraftInvoice}
    (h : mkDraft tenant period price events = .ok inv) :
    Balanced inv.val
```

Writes do not recompute the total at runtime to "make sure". They take a `Checked` row built from that proof (and from `finalize_preserves_balanced`, `pay_preserves_balanced`, `void_preserves_balanced` on the way out of draft):

<!-- check: excerpt examples/billing/Billing/Schema.lean -->
```lean
def InvoiceRow.checked (inv : Invoice) (h : Balanced inv) : Checked InvoiceRow :=
  Checked.of (InvoiceRow.ofInvoice inv) (InvoiceRow.Invariant_ofInvoice inv h)
```

Acme reports quantity 3 at 10¢. The invoice total is 30 (`3 × 10¢ = 30`). Opening the same period again replays that draft (`same period replays`):

```http
HTTP/1.1 201 Created
Location: /invoices/1

{"id":1,"lines":[{"amount":30,"eventId":"evt_1","quantity":3,"unitPrice":10}],"period":{"month":9,"year":2026},"status":"draft","total":{"amount":30,"currency":"usd"}}
```

## A finalized invoice does not change

The lifecycle is a family of subtypes. `replaceLines` accepts a `DraftInvoice`. `pay` and `voidInvoice` accept a `FinalizedInvoice` and return `PaidInvoice` / `VoidInvoice`. There is no function that edits the lines of a sealed invoice.

<!-- check: excerpt examples/billing/Billing/Domain.lean -->
```lean
abbrev DraftInvoice := { inv : Invoice // inv.status = .draft }
abbrev FinalizedInvoice := { inv : Invoice // inv.status = .sealed .finalized }
abbrev PaidInvoice := { inv : Invoice // inv.status = .sealed .paid }
abbrev VoidInvoice := { inv : Invoice // inv.status = .sealed .void }
```

<!-- check: excerpt examples/billing/Billing/Domain.lean -->
```lean
def pay (inv : FinalizedInvoice) : PaidInvoice :=
  ⟨{ inv.val with status := .sealed .paid }, rfl⟩

def voidInvoice (inv : FinalizedInvoice) : VoidInvoice :=
  ⟨{ inv.val with status := .sealed .void }, rfl⟩
```

The only moves out of `finalized` are those two, and they keep the lines.

<!-- check: signature Billing.pay_next -->
```lean
theorem pay_next (inv : FinalizedInvoice) :
    Next inv.val.status (pay inv).val.status
```

<!-- check: signature Billing.pay_keeps_lines -->
```lean
theorem pay_keeps_lines (inv : FinalizedInvoice) :
    (pay inv).val.lines = inv.val.lines ∧ (pay inv).val.total = inv.val.total
```

`void_next` and `void_keeps_lines` match for void. HTTP `/pay` and `/void` require `finalized` and write those functions. Paying a draft is 409 (`pay while draft 409`). After finalize and pay the total is still 30 (`lines unchanged at finalize`, `lines unchanged at pay`). Void after pay is 409.

```http
HTTP/1.1 409 Conflict
Content-Type: application/problem+json

{"detail":"invoice is not finalized","status":409,"title":"Conflict","type":"about:blank"}
```

## Tenant isolation

A bearer token is the tenant's API key. `lookupTenant` is the trusted exception: it reads `TenantRow` unscoped, because there is no actor yet (DESIGN.md §7.5). After that, every usage and invoice program is scoped.

<!-- check: excerpt examples/billing/Billing/Api.lean -->
```lean
def readInvoice (me : Auth Tenant) (id : Path InvoiceId) :
    Read BillingDb (Except BillingError InvoiceView) :=
  ReadAs.forAuth me fun _a => do
    match ← ReadAs.get InvoiceRow (iref id.val) with
    | some s =>
      match invoiceViewOf s with
      | some v => return .ok v
      | none => return .error .hidden
    | none => return .error .hidden
```

`ReadAs.get` adds the policy to the SQL `WHERE`. Another tenant's invoice is `none`, the same 404 as a missing id (`other's invoice ≡ missing`). Writes go through `TxnAs`: private constructor, insert and update only with `Owns` evidence, `Seen` handles only for rows the policy admits.

Beta reading Acme's event:

```http
HTTP/1.1 404 Not Found
Content-Type: application/problem+json

{"status":404,"title":"Not Found","type":"about:blank"}
```

That 404 is tested (`beta cannot read acme's event`, `other's event ≡ missing (status)`). It is not a theorem over the database.

## What a mistake looks like

Mounting ingest as GET is a type error. The compiler, pinned with `#guard_msgs` in `Billing/Api.lean`:

```text
error: a GET or HEAD endpoint must not change state, but this handler's effect is `writes`. Return `Reads σ _` (or a pure value), or use POST, PUT, PATCH or DELETE.
⊢ (Handler.effect (DbState BillingDb)
      (Auth Tenant → Body UsageBody → LeanApi.Tx BillingDb BillingError (Replayed (Created UsageView)))).Safe
```

The refused program is this:

<!-- check: excerpt examples/billing/Billing/Api.lean -->
```lean
example : DbEndpoint BillingDb := .get "/usage" ingestUsage
```

Editing a finalized invoice's lines is the same kind of refusal. `replaceLines` wants a draft:

```text
error: Application type mismatch: The argument
  inv
has type
  FinalizedInvoice
but is expected to have type
  DraftInvoice
in the application
  replaceLines inv
```

<!-- check: excerpt examples/billing/Billing/Domain.lean -->
```lean
example (inv : FinalizedInvoice) (ls : List Line) (htot : sumAmounts ls ≤ maxTotal)
    (hlen : ls.length ≤ maxLines) : DraftInvoice :=
  replaceLines inv ls htot hlen
```

Paying a draft does not type-check (`pay inv` in `Domain.lean`). Forging a `TxnAs` or `Seen` from another module is refused (`Billing/Bypass.lean`: those constructors are private). A table without a policy is not in the view: `ReadAs.all TenantRow` fails to synthesize `Policy BillingDb Tenant TenantRow`.

<!-- check: compile -->
```lean
example (log : List UsageEvent) (e : UsageEvent) :
    ingest (ingest log e) e = ingest log e :=
  ingest_idem log e
```

## What exactly is guaranteed

No claim here is stronger than its evidence. There are no theorems over `DbState`, `Read.denote`, or `Txn.denote`. At LeanDB `afe4544`, those would be vacuous (review H1).

### Proved

Pure domain functions, audited with `#print axioms` (no `sorry`, no `native_decide`):

- `ingest_idem`, `ingest_already`, `ingest_new`, `hasEvent_snoc`: a log counts each `(tenant, eventId)` once.
- `rateLog_append`, `rateLog_ingest_idem`, `Line.rate_priced`: rating adds over concatenation and does not double-count a repeated ingest.
- `mkDraft_balanced`, `mkDraft_ok`: a draft built by `mkDraft` is balanced.
- `finalize_keeps_lines`, `pay_keeps_lines`, `void_keeps_lines`, `finalize_preserves_balanced`, `pay_preserves_balanced`, `void_preserves_balanced`: transitions keep lines, total, and the invariant.
- `pay_next`, `void_next`: the only constructed moves out of `finalized` are to `paid` and `void`.
- `InvoiceRow.invariant_ofInvoice`, `InvoiceRow.toInvoice_ofInvoice_id`: the stored invariant is the domain's `Balanced`, and the row mapping round-trips.

### Enforced by the types

The compiler refuses, pinned with `#guard_msgs`:

- `replaceLines` on a `FinalizedInvoice`; `pay` on a `DraftInvoice`.
- `.get "/usage" ingestUsage`: a GET cannot return `Tx`.
- `TxnAs.mk` and `Seen.mk` from outside `Policies.lean`.
- `ReadAs.all TenantRow`: no policy, default deny.
- `PolicyView.Actor` constructed in application code.

Handlers take `Auth Tenant`, `EventId`, `Quantity`, `Instant`, `Money .usd`. There is no stringly-typed status and no bare `Nat` for money.

### Tested

`tests/Tests/Billing.lean`, section `billing: ingest once, isolate tenants, freeze finalized invoices`:

- `ingest 201`, `resend marked replay`, `same id, other quantity: still first quantity`, `concurrent ingest all 201`, `GET after race is the original quantity`.
- `3 × 10¢ = 30`, `same period replays`, `2 × 25¢ = 50`.
- `pay while draft 409`, `lines unchanged at finalize`, `lines unchanged at pay`, `void after pay 409`.
- `beta cannot read acme's event`, `other's event ≡ missing (status)`, `beta cannot read acme's invoice`, `other's invoice ≡ missing (body)`, `no auth 401`.

### Planned

DESIGN.md §7.5, which needs LeanDB M15 (`DbState` with real content, execution that agrees with the meaning):

- Restricted reads: a program over `S.As p` observes only rows `p`'s policy admits.
- Write confinement: a transaction over `S.As p` leaves every other tenant's row unchanged.
- Noninterference for every route, from the database layer's laws, with no per-endpoint isolation proof.
- Coverage: `api!` refuses an unscoped program unless it is marked trusted, so the served routes and the proved routes are the same set.

Until then, isolation and "exactly once" at SQL are type-enforced in these handlers, and tested, not proved about the running database.
