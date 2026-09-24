# billing: usage events counted exactly once

A tiny usage-based billing service on LeanAPI and LeanDB: tenants report
usage, invoices rate that usage, and four rules are declared once and
enforced at every boundary.

```
lake build billing
./.lake/build/bin/billing --port 8080 --db billing.sqlite
```

Demo tenants are seeded on open:

| API key | Price |
|---|---|
| `acme-live-key` | 10¢ per unit |
| `beta-live-key` | 25¢ per unit |

```bash
# count an event once; a resend is a replay
curl -sS -D - -H "Authorization: Bearer acme-live-key" \
  -H "Content-Type: application/json" \
  -d '{"eventId":"evt_1","quantity":3,"occurredAt":1727136000,"period":{"year":2026,"month":9}}' \
  http://127.0.0.1:8080/usage

# same body again: 201, Idempotent-Replayed: true, still one event
curl -sS -D - -H "Authorization: Bearer acme-live-key" \
  -H "Content-Type: application/json" \
  -d '{"eventId":"evt_1","quantity":3,"occurredAt":1727136000,"period":{"year":2026,"month":9}}' \
  http://127.0.0.1:8080/usage

# invoice for September: 3 × 10¢ = 30
curl -sS -D - -H "Authorization: Bearer acme-live-key" \
  -H "Content-Type: application/json" \
  -d '{"period":{"year":2026,"month":9}}' \
  http://127.0.0.1:8080/invoices
```

## API

| Route | Notes |
|---|---|
| `POST /usage` | Body `eventId`, `quantity`, `occurredAt` (UTC unix seconds), `period`. Duplicate `(tenant, eventId)` replays the first answer |
| `GET /usage/{eventId}` | Own events only; another tenant's id is 404 |
| `POST /invoices` | Draft for a period, unique `(tenant, period)`. Lines are quantity × unit price; total is their sum |
| `GET /invoices/{id}` | Own invoices only |
| `POST /invoices/{id}/finalize` | `draft → finalized`. Lines stay |
| `POST /invoices/{id}/pay` | `finalized → paid` |
| `POST /invoices/{id}/void` | `finalized → void` |

Authorization is `Authorization: Bearer <api-key>`. Missing or unknown keys are 401.

## Layout

| File | What |
|---|---|
| `Billing/Domain.lean` | Pure types, ingest, rating, invoice lifecycle, theorems |
| `Billing/Schema.lean` | LeanDB entities, unique indexes, `Balanced` as a row invariant, `Checked` from proofs |
| `Billing/Policies.lean` | `Policy` per table, `TxnAs` write view, `InvoiceView` projection |
| `Billing/Bypass.lean` | Compile-time refusals of unscoped writes (private constructors) |
| `Billing/Api.lean` | Typed endpoints over `Read` / `Tx` |

## Design

**Event counted exactly once.** Unique index `UsageEventRow.byTenantEvent` on `(tenant, eventId)`. Inserting a duplicate is `InsertError.duplicate`; the handler looks the holder up through the tenant's view and answers as a replay. The pure function `ingest` is idempotent (`ingest_idem`); rating it twice does not double-count (`rateLog_ingest_idem`).

**Total equals the lines.** `invariant Balanced` on the domain invoice; `InvoiceRow.invariant` is `Balanced.holdsB` of the mapped row. Writes take `Checked InvoiceRow` from `mkDraft_balanced` / `finalize_preserves_balanced` / `pay_preserves_balanced` / `void_preserves_balanced`. No runtime recomputation of the total.

**Finalized invoices do not change.** `replaceLines` accepts only `DraftInvoice`. `pay` and `voidInvoice` accept only `FinalizedInvoice` and keep the lines (`pay_keeps_lines`, `void_keeps_lines`). The only HTTP updates of a finalized invoice are `/pay` and `/void`, which write a new status on the same lines.

**Tenant isolation.** `Policy BillingDb Tenant UsageEventRow` and `InvoiceRow`: `r.val.tenant == tref t.id`, pushed into SQL. `TenantRow` has no policy (default deny); authentication looks it up unscoped by API key, the trusted exception of DESIGN §7.5. Writes go through `TxnAs`: private constructor, `Owns` evidence on insert/update, `Seen` handles only for rows the policy admits.

## What is guaranteed

See [docs/blog/billing.md](../../docs/blog/billing.md) for the four-heading evidence list. In short:

- **Proved** (pure functions): `ingest_idem`, `rateLog_append`, `rateLog_ingest_idem`, `mkDraft_balanced`, `pay_keeps_lines`, `void_keeps_lines`, `pay_next`, `void_next`, codec round-trips.
- **Enforced by the types:** `replaceLines` refuses a finalized invoice; `pay` refuses a draft; a GET cannot return `Tx`; unscoped writes and a table without a policy do not compile (`#guard_msgs` in `Domain.lean`, `Api.lean`, `Policies.lean`, `Bypass.lean`).
- **Tested:** duplicate ingest is a replay; isolation 404; finalized lines stay put (`tests/Tests/Billing.lean`).
- **Planned:** DESIGN §7.5 restricted-reads / write-confinement theorems, which need LeanDB M15 (`DbState` has no content in proofs today).
