# billing: usage events counted exactly once

A tiny usage-based billing service on LeanAPI and LeanDB: tenants report
usage, invoices rate that usage, and four rules are stated as domain
functions and types. Handlers and SQL are written to follow them. Policy
`rule` and SQL `scope` are still two fields; see the post.

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
| `POST /usage` | Body `eventId`, `quantity`, `occurredAt` (UTC unix seconds), `period`. Same id and same payload replays; same id, different payload is 409 |
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

**Event counted exactly once.** Unique index `UsageEventRow.byTenantEvent` on `(tenant, eventId)`. Inserting a duplicate is `InsertError.duplicate`; the handler runs `ingestChecked` on the stored row: same payload is a replay, a different payload is `eventConflict` (409, not 422: the body is well-typed, the id is already bound). The problem does not include the stored event. Pure `ingest` is idempotent (`ingest_idem`); `ingestChecked_replay_iff` / `ingestChecked_conflict_iff` say when each decision happens.

**Total equals the lines.** `invariant Balanced` on the domain invoice; `InvoiceRow.invariant` is `Balanced.holdsB` of the mapped row. Writes take `Checked InvoiceRow` from `mkDraft_balanced` / `finalize_preserves_balanced` / `pay_preserves_balanced` / `void_preserves_balanced`. No runtime recomputation of the total.

**Finalized invoices do not change.** `replaceLines` accepts only `DraftInvoice`. `pay` and `voidInvoice` accept only `FinalizedInvoice` and keep the lines (`pay_keeps_lines`, `void_keeps_lines`). The only HTTP updates of a finalized invoice are `/pay` and `/void`, which write a new status on the same lines.

**Tenant isolation.** `Policy.rule` on usage and invoices is `r.val.tenant == tref t.id`. `usage_rule_ofEvent` / `invoice_rule_ofInvoice` prove that, through the row mapping, this is domain ownership (`e.tenant = p.id`). SQL `scope` is written to look the same; that it matches `rule` is not proved. `TenantRow` has no policy (default deny); authentication looks it up unscoped by API key, the trusted exception of DESIGN §7.5. Writes go through `TxnAs`: private constructor, `Owns` evidence on insert/update, `Seen` handles only for rows the policy admits.

## What is guaranteed

See [docs/blog/billing.md](../../docs/blog/billing.md) for the four-heading evidence list. In short:

- **Proved** (pure functions): `ingest_idem`, `ingestChecked_fresh_iff`, `ingestChecked_replay_iff`, `ingestChecked_conflict_iff`, `usage_rule_ofEvent`, `invoice_rule_ofInvoice`, `mkDraft_balanced`, `pay_keeps_lines`, `void_keeps_lines`, `pay_next`, `void_next`.
- **Enforced by the types:** `replaceLines` refuses a finalized invoice; `pay` refuses a draft; a GET cannot return `Tx`; unscoped writes and a table without a policy do not compile (`#guard_msgs` in `Domain.lean`, `Api.lean`, `Policies.lean`, `Bypass.lean`).
- **Tested:** duplicate ingest is a replay; same id, different payload is 409; isolation 404; finalized lines stay put (`tests/Tests/Billing.lean`).
- **Planned:** `scope` matching `rule`; DESIGN §7.5 restricted-reads / write-confinement, which need LeanDB M15.
