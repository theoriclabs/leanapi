# Integrity across boundaries: the domain model and the systems around it

Status: design exploration, 2026-09-23.

Most backend code is not business logic. It is moving data across boundaries:
- HTTP request to domain value;
- domain value to database row, row back to value, value to JSON;
- event to a queue and on to a consumer;
- value to a cache, a search index, a warehouse, a CSV export, a third-party API, a log line.

Each system on the other side has its own schema, its own value space, its own rules and its own idea of time. They change on their own schedules. The code at each crossing is written by hand, tested by example, and drifts. Integrity problems accumulate in the gaps.

**The goal:** the domain model maps *tightly* onto every external system it touches, and the compiler reports every violation it can know about. What it cannot know statically is caught at build time against the real systems, or at the boundary at runtime, and nowhere later.

Part 1 collects examples. Part 2 names the patterns. Part 3 proposes solutions, and Part 4 says what the compiler can and cannot check.

---

## Part 1. Examples

Real incidents and everyday bugs, including some in this repository. Each is a place where two layers disagreed about the same data.

### A. Representation: the value spaces differ

| # | Boundary | What goes wrong |
|---|---|---|
| A1 | JSON → JavaScript | 64-bit ids become IEEE doubles; above 2^53 they silently change. Twitter had to add `id_str` next to `id`. **Here:** private-games serialises game ids up to 2^63−1 as JSON numbers (`gameJson`), so a browser client would corrupt ids above 2^53 |
| A2 | Code → database integer | A counter outgrows its column: YouTube's view count for *Gangnam Style* passed 2^31−1; Postgres `serial` primary keys run out at 2^31. **Here:** LeanDB's `Nat` codec wrapped at 2^63, fixed in LDB-18 by refusing (and still clamping on some paths) |
| A3 | Float → narrower integer | Ariane 5 flight 501: a 64-bit float converted to a 16-bit integer overflowed in code reused from Ariane 4, whose flight profile never produced such values |
| A4 | Money across layers | Floats for currency, `NUMERIC(10,2)` rounding, a payment API in minor units (cents) while the app thinks in major units, currencies with 0 or 3 decimal places (JPY, KWD) |
| A5 | Time units | JWT `exp` in seconds and JavaScript dates in milliseconds; epoch seconds read as milliseconds land in 1970 |
| A6 | Time zones | `timestamp without time zone` interpreted in the server's zone; local times across DST; ISO strings with and without offsets compared as strings; the year-2038 limit of 32-bit `time_t` and MySQL `TIMESTAMP` |
| A7 | Text length | `VARCHAR(255)` counts characters in one engine and bytes in another; MySQL in non-strict mode silently truncates; a search index truncates long fields |
| A8 | Text encoding | MySQL's `utf8` holds only 3-byte characters, so emoji fail or corrupt rows until `utf8mb4`; mojibake from Latin-1 assumed as UTF-8 |
| A9 | Binary encodings | base64 vs base64url vs hex; padding required by one side and rejected by the other |
| A10 | Floats in JSON | `NaN` and `Infinity` are not valid JSON; one serializer emits them, another rejects them; `-0` round-trips differently |
| A11 | Physical units | Mars Climate Orbiter was lost because one system produced pound-force seconds and another expected newton seconds |

### B. Constraints: rules enforced on one side only, or differently

| # | Boundary | What goes wrong |
|---|---|---|
| B1 | Browser ↔ API ↔ database | Three validators for "email": a regex in the form, another in the API, none in the database. Data from an admin import passes none of them |
| B2 | Application ↔ database uniqueness | "Check then insert" in the application without a unique index races into duplicates. The reverse: a unique index the application doesn't map, so a clash becomes a 500 |
| B3 | Length limits | The API accepts 255 characters, the column holds 100: a 500 at insert, found in production |
| B4 | Required fields | Optional in the API and `NOT NULL` in the database (a 500), or a database default quietly fills in a missing value the domain never had |
| B5 | Invariants in ORM hooks | Rails validations and callbacks are skipped by `update_all`, raw SQL, bulk imports and migrations, so rows that "can't exist" do |
| B6 | Denormalised data | An order's stored total differs from the sum of its lines; a counter cache differs from the count |
| B7 | References across services | An order refers to a user in another service's database: no foreign key is possible, and deletions leave dangling references |
| B8 | Enumerations | A new status is written by new code before the database `CHECK` (or the old consumers) knows it; an old mobile app crashes on an unknown enum value |

### C. Semantics: same shape, different meaning

| # | Boundary | What goes wrong |
|---|---|---|
| C1 | SQL `NULL` | Three-valued logic: `WHERE status <> 'x'` drops `NULL` rows; `NOT IN (…, NULL)` is never true; Oracle treats `''` as `NULL` |
| C2 | Absent vs `null` in JSON | In a PATCH, "field absent" means *leave it* and `null` means *clear it*; a decoder that maps both to `none` makes clearing impossible (or unintended) |
| C3 | Collation | MySQL's default collation is case-insensitive, so `Bob` and `bob` clash on a unique index while the application treats them as different users; trailing spaces compare equal under PAD SPACE |
| C4 | Unicode normalisation | `é` as one code point (NFC) or as `e` plus a combining accent (NFD, the macOS filesystem's form). Two "identical" usernames pass a unique index; lookups miss |
| C5 | Configuration values | YAML 1.1 reads the country code `NO` as `false` (the "Norway problem"); environment variables where `"false"` is truthy |
| C6 | Spreadsheets | Excel turns gene names such as SEPT1 into dates, and strips leading zeros from postcodes; locale date formats (`01/02/03`) |
| C7 | Last write wins | Two systems "resolve" conflicts by timestamp while their clocks disagree; an older update overwrites a newer one |

### D. Evolution: the two sides change at different times

| # | Boundary | What goes wrong |
|---|---|---|
| D1 | Code ↔ migration | During a rolling deploy, old code writes a column the new migration renamed; a column is dropped while an old version still reads it |
| D2 | Model ↔ real schema | Someone added a column by hand in production; migrations were squashed; the ORM's model and the database disagree and nobody knows |
| D3 | API ↔ clients | A response field is renamed; mobile clients from two years ago are still in use |
| D4 | Queue ↔ consumers | A producer ships a new message format while old consumers run. Months-old messages are replayed from a retained topic. One undecodable "poison" message blocks a partition |
| D5 | Cache ↔ code | Objects serialized by the old version (pickle, Java serialization, JSON of an old shape) fail to deserialize after a deploy, or deserialize wrongly |
| D6 | Search index | Elasticsearch infers a field's type from the first document: `long`, then a string arrives and every later document is rejected |
| D7 | Event store | Every event ever written must stay decodable; the upcasters that translate old events are untested code |
| D8 | Backups | Restoring last month's backup into this month's code |
| D9 | Configuration | Knight Capital (2012) repurposed a feature flag; one server still ran old code for which the flag meant something else. Around $440M was lost in 45 minutes |
| D10 | Stored responses | **Here:** idempotency receipts store a rendered response and replay it verbatim, even after the API's response format changes |

### E. Delivery and consistency: two systems, one fact

| # | Boundary | What goes wrong |
|---|---|---|
| E1 | Database + queue | "Write the row, then publish the event": a crash in between loses the event, or the publish succeeds and the transaction rolls back (a phantom event). This is the reason for the outbox pattern |
| E2 | At-least-once delivery | A consumer processes a message twice and charges twice; ordering holds only within a partition |
| E3 | Cache | Stale data after an update; worse, cached data served after the user's permission was revoked (an isolation leak) |
| E4 | Read replicas | Replication lag breaks read-your-writes |
| E5 | Derived stores | The search index, warehouse and analytics store lag behind or diverge; a GDPR deletion misses the index, the backups and the logs |
| E6 | Third-party API | A payment webhook arrives before your transaction committed, or twice, or out of order; the provider's API version is pinned per account |
| E7 | Timeouts | The client times out, but the server committed. **Here:** LeanAPI's `timeout` answers 504 while an admitted command can still commit |
| E8 | Retries | An HTTP client retries a non-idempotent POST |

### F. Identity: which thing, in which system

| # | Boundary | What goes wrong |
|---|---|---|
| F1 | Ids as plain integers or strings | A user id passed where an order id was expected; both are `Int` |
| F2 | External ids | Provider ids stored as strings: a `cus_…` used where an `acct_…` belongs; the provider changes the format |
| F3 | Emails and handles | Case sensitivity of the local part; trailing whitespace; Unicode lookalikes |
| F4 | UUIDs | String vs binary storage, v4 vs v7 ordering assumptions, case of hex digits |

### G. Exposure: data where it must not be

| # | Boundary | What goes wrong |
|---|---|---|
| G1 | Logs and traces | Personal data or tokens in log lines, error messages and traces, which have longer retention and wider access than the database |
| G2 | Multi-tenant tables | One query forgets the tenant filter |
| G3 | Cache keys | A key without the user or tenant serves one user's data to another |

### H. Bypass: paths around the checked path

| # | Boundary | What goes wrong |
|---|---|---|
| H1 | Raw SQL and admin consoles | Writes that skip every validation and invariant |
| H2 | Imports and data fixes | A CSV import or a one-off script writes rows the domain would never produce |
| H3 | Migrations | A data migration produces rows that violate a newly added invariant, or an old one |
| H4 | Tools talking to the database | **Here:** LeanDB's CLI and `leandb serve` write through the typed `insert`/`update`, so invariants are checked. The paths around them: raw SQL through `untrackedSqlite`, the `sqlite3` shell on the file, and `restore`, which checks the file's schema fingerprint but not its rows |

---

## Part 2. Patterns

The examples fall into a few classes of mismatch. Each class needs a different kind of check.

| Class | Question at the boundary | Examples |
|---|---|---|
| **Representation** | Can every valid domain value be represented on the other side, and read back unchanged? | A1–A11 |
| **Constraint** | Do both sides accept exactly the same values? | B1–B8 |
| **Semantics** | Do equality, ordering, absence and comparison mean the same thing on both sides? | C1–C7 |
| **Evolution** | Can each version read what every other live version writes, for as long as that data lives? | D1–D10 |
| **Delivery** | Is each fact recorded everywhere it must be, once, in order, or is the divergence explicit? | E1–E8 |
| **Identity** | Does each reference denote the thing and the system it claims to? | F1–F4 |
| **Exposure** | Does each system hold only what it is allowed to hold? | G1–G3 |
| **Bypass** | Does every path into the data go through the checks? | H1–H4 |

Three observations shape the solution:

1. **The domain types are almost always the strongest description of the data.** `Title`, `GameId` and `Money JPY` know rules that `VARCHAR`, `BIGINT` and JSON `number` do not. Integrity is lost at the crossing, where a strong type meets a weak one and the conversion is hand-written.
2. **Most mismatches are decidable once both sides are written down.** "Can a `Title` of up to 200 characters fit in `VARCHAR(100)`?" "Does this collation distinguish case?" "Is adding a required field backward compatible?" These are questions about two schemas. The difficulty is that one of the schemas usually lives outside the program.
3. **What cannot be decided statically has a last responsible moment.** The live schema can differ from the declared one; a message can arrive malformed; a clock can be wrong. These must be caught at build time against the real system, at startup, or at the boundary at runtime, and never later, inside the domain.

---

## Part 3. Solutions

The idea is one discipline applied to every external system:

> **Every external system is described by a schema, as a Lean value. Every crossing is a *mapping* between a domain type and that schema, and the mapping carries proofs. Schemas are pinned, checked against the real system, and checked for compatibility when they change.**

### 3.1 External schemas as values

Each kind of external system gets a small description language, as data:

| System | Its schema describes |
|---|---|
| SQL table | columns with SQL types, sizes, nullability, collation; `CHECK`, `UNIQUE`, foreign keys; defaults |
| JSON over HTTP (ours or a third party's) | an OpenAPI/JSON Schema object: types, formats, lengths, patterns, required and nullable fields, enums |
| Queue topic | the payload schema (Avro, Protobuf or JSON), the partition key, and the **delivery semantics** (at most once, at least once, ordered by key) |
| Cache keyspace | the key's shape (which parts identify the user or tenant), the value schema, the TTL |
| Search index | field mappings, analyzers, which fields are stored |
| File format | CSV columns, quoting, encoding, date and number formats |
| Client runtime | the value space of the consumer: a JavaScript client's numbers are IEEE doubles |

**Where a schema comes from.** A schema is either declared in Lean (our own tables, topics and APIs) or **imported at build time from the system that owns it**: a database's catalogue, a schema registry, a provider's OpenAPI file. An imported schema is written into the repository as a pinned snapshot, like a lock file. Diffs are reviewed like code, so upstream changes show up as reviewable changes, not as production incidents.

LeanDB already does parts of this: entities declare tables, `Import.introspect` reads a live SQLite schema, and a schema fingerprint (DDL, JSON shapes, enum variants, invariant names) is checked when a database is opened or restored and when a client connects. `unique%` checks index fields against the entity at compile time.

### 3.2 Mappings that carry their proofs

A crossing is a mapping, not a pair of hand-written functions:

```lean
structure Mapping (D : Type) (S : Ext.Schema) where
  encode : D → S.Value
  decode : S.Value → Except (DecodeError S) D
  /-- Every domain value fits: range, length, precision, character set. -/
  fits : ∀ d, S.Valid (encode d)
  /-- Reading back what was written gives the same value. -/
  roundTrip : ∀ d, decode (encode d) = .ok d
  /-- The decoder refuses exactly what is not a domain value (no silent repair). -/
  exact : ∀ v, S.Valid v → (∃ d, decode v = .ok d) ∨ decode v = .error (reason v)
```

- **Mappings are derived field by field** for records, like `deriving LeanDb.Entity`. The proofs are discharged automatically when the domain type is at most as wide as the external type.
- **When it isn't, the compiler says where.** "`Title` admits 300 characters; column `notes.title` holds `VARCHAR(200)`: narrow `Title`, widen the column, or map through a refinement." That catches A2, A3, A7 and B3 before anything runs.
- **`fits` is per consumer.** The same `GameId` maps to `BIGINT` in SQLite, but to a JSON *string*, or to a number bounded by 2^53, for a JavaScript client (A1). The browser client's schema says its numbers are doubles, so a mapping of a 64-bit id to a JSON number does not type-check for that consumer.
- **`decode`'s failure type names the field and the rule**, as LeanAPI's `FieldError` does today, so bad data is refused at the edge with a precise reason (B1, H2).

### 3.3 Constraints in correspondence

For each constraint, the mapping states whether it is **enforced on both sides and agrees**, or **enforced on one side, and which**:

- **Uniqueness.** A domain `unique User.byName` corresponds to a unique index only if the database's equality on the key agrees with the domain's: `∀ a b, dbEq (enc a) (enc b) ↔ a.name = b.name`. Under a case-insensitive collation that is false, unless the domain key is the case-folded, NFC-normalised name (a `Handle` type). The proof obligation surfaces C3 and C4 at compile time.
- **Absence.** `Option τ` maps to a nullable column and nothing else; a non-`Option` field maps to `NOT NULL` with no default (B4). For JSON PATCH, "absent" and "`null`" are different constructors (`Patch.keep`, `Patch.clear`, `Patch.set v`), so C2 cannot be expressed wrongly.
- **Enumerations.** A closed Lean inductive maps to a `CHECK (x IN …)`, a JSON Schema `enum`, or a Protobuf enum. Unknown values from the outside are a typed decoding failure, never a crash, and never a silent default (B8).
- **Invariants that a system cannot express** (an order's total equals the sum of its lines, B6) are listed as enforced on the domain side only. The compiler then requires that every writer into that system goes through the domain: the H-class paths are either typed or refused.

### 3.4 Semantic types instead of primitives

Many semantic mismatches disappear when the domain never uses a primitive for a meaning:

| Instead of | Use | Which then maps to |
|---|---|---|
| `Nat` seconds or milliseconds | `Instant` (UTC, a declared unit) and `Duration` | a column or JSON field whose unit is part of its schema (A5, A6) |
| wall-clock `String` | `LocalDateTime` together with a `Zone` | never compared across zones without conversion |
| `Float` for money | `Money (c : Currency)`, whose scale depends on the currency (a dependent type) | minor units, with the scale checked per currency (A4) |
| `String` for a login | `Handle`: trimmed, NFC-normalised, case-folded | the unique index, with the equality correspondence above (C3, C4, F3) |
| `Int` ids | `Id α`, `Ref α`, typed external ids (`Stripe.Id .customer`) with prefix validation | columns and JSON fields that cannot be confused (F1, F2) |
| free-form quantities | values with units in the type | only same-unit arithmetic compiles (A11) |

### 3.5 Evolution as a checked relation between schemas

Schemas are versioned values, and compatibility is a decidable relation between them, defined per kind of system:

```lean
def Compatible (old new : Ext.Schema) : Prop :=
  (∀ v, old.Valid v → new.Readable v) ∧     -- new code reads old data (backward)
  (∀ v, new.Valid v → old.Readable v)       -- old code reads new data (forward)
```

- **A rolling deploy is a sequence of schemas,** each compatible with its neighbours: *expand* (add a nullable column, add a field consumers ignore), *migrate* (backfill; both versions read and write), *contract* (remove the old form). The compiler rejects a change whose steps are not pairwise compatible: renaming a column in one step is D1, and it doesn't compile.
- **Data with a long life** (queue retention, event stores, caches, backups, stored responses) must be readable by every version that can meet it. Old schema snapshots stay in the repository, and upcasters are total functions with round-trip proofs. CI decodes a fixture of every retained version (D4, D5, D7, D8, D10).
- **Configuration is a schema too,** with a mapping from the file format. An unknown key, a repurposed flag or `NO` read as a boolean is a decoding failure at startup (C5, D9).

### 3.6 Delivery semantics in effect types

What a transport guarantees is part of its schema, and the type of the code at each end must match it:

- **At-least-once sources need idempotent consumers.** A consumer of an at-least-once topic must be *proved* idempotent, or run through a keyed receipt: the same `keyed` pattern as the HTTP API, or the `Keyed` transformer in `LeanApi/Props/Keyed.lean` (E2, E6).
- **No dual writes.** Inside a `Txn`, the only way to "publish" is to append to an outbox table in the same transaction. A relay delivers from the outbox at least once, with a dedupe key. A direct publish has no place in the `Txn` effect, so E1 cannot be written.
- **Derived stores are projections.** A cache, a search index or a read model is declared as a function of the source of truth, with its staleness in the type (`Stale (≤ 30 s) α`). Reads through a cache must be keyed by the principal, a proof obligation that makes E3 and G3 compile errors. The isolation theorems then extend over the cache.
- **Timeouts are outcomes.** A command's result type includes "unknown, check again" wherever a timeout can race a commit (E7). Clients get a typed way to ask, by idempotency key, what happened.

### 3.7 Identity and exposure as types

- **Identity.** Typed ids everywhere (F1, F2), including other systems' ids. References across systems are declared (`Ref Stripe.Customer`). The compiler generates the **reconciliation check** that finds dangling ones, since no foreign key can (B7).
- **Exposure.** Data classification is part of the type (`Pii α`, `Secret α`). Mappings into logs, traces, analytics and error messages must redact or refuse them, and the compiler finds the path that doesn't (G1). Tenant scoping is already a proof obligation in LeanAPI's isolation theorems (G2).

### 3.8 One gate for every writer

Every path into a system goes through its mapping:
- the API, CLI tools, imports, migrations, restores and admin actions;
- the same `Checked` values and the same typed writes.

Paths that cannot (raw SQL, a vendor console) are declared as bypasses, and the evidence record lists them. After a bypass or a restore, a **row-level verification pass** (decode every row under the current mappings and check every invariant) re-establishes the well-formedness the proofs assume (H1–H4). LeanDB's `Conn.verify` already does the schema-level half on open and restore.

---

### 3.9 Access rules are business rules too

Who may see or change which rows is the business rule that crosses the most boundaries: HTTP, the handler, the query, the database, and every copy of the data (caches, indexes, logs). The same discipline applies:
- declare the rule once, with the schema, as a policy;
- let the authenticated actor flow from the API into the type of every database program;
- have the database layer apply the policy to every read and write;
- prove isolation once, for every route.

This is row-level security, typed and proved. [DESIGN.md §7.5](../DESIGN.md) sets it as a goal.

## Part 4. What the compiler checks, and what it cannot

| Check | When | What it catches |
|---|---|---|
| Mapping obligations (`fits`, `roundTrip`, constraint correspondence) | compile time | A1–A11, B3, B4, B8, C3, C4 |
| Exhaustive handling of decoding and write failures | compile time | B2, B8, D4 |
| Compatibility of declared schema versions | compile time | D1, D3, D4, D5, D10 |
| Effect rules (no dual writes, idempotent consumers, keyed caches) | compile time | E1, E2, E3, G3 |
| Data classification reaching logs or analytics | compile time | G1 |
| Pinned external schemas against the live systems | build time (CI) | D2, D6, and upstream changes to third-party APIs |
| Schema fingerprint handshake | startup | a deploy against the wrong database, version skew |
| Decoding at untrusted boundaries | runtime, at the edge | malformed input, poison messages, drifted data (B1, H2), with typed errors |
| Reconciliation across systems | periodic | dangling cross-system references, divergence of derived stores (B7, E5) |
| Row-level verification after bypasses and restores | on demand | H1, H3, D8 |

**What it cannot check:**
- that the real system behaves as its schema says (SQLite honours `UNIQUE`; the provider's API matches its OpenAPI file);
- clock accuracy;
- data written by tools outside the build.

Those are trusted or checked at runtime, and the evidence record says which, as it does for LeanDB's execution today.

---

## Part 5. How this fits what exists

- **LeanDB** already has entity codecs, `ColCodec` (round-trips proved by the consumer where needed, as private-games' `nat_roundtrip`), `SmartCtor` validation on read, invariants, schema fingerprints and live-schema import. [QUERIES.md](QUERIES.md) makes tables typed values with typed failures. What is missing, from the list above:
  - `fits` as a law of `ColCodec` (LDB-18 is the first instance);
  - collation and normalisation in key equality;
  - one way to declare indexes (`unique%` is checked at compile time; `IndexSpec.columns` strings only when the database opens);
  - row-level verification (`Conn.verify` checks the schema fingerprint, not the rows);
  - compatibility of schema versions (LeanDB's migrations are the starting point).
- **LeanAPI** has typed request and response codecs, `FieldError` locations, OpenAPI generation, `ToProblem` with typed statuses, and the property library. What is missing:
  - a JavaScript-client schema with a double-precision number space (A1, which affects private-games today);
  - absent-vs-`null` in PATCH bodies (C2);
  - compatibility checks between published API versions (D3), including stored receipts (D10).
- **LeanHttp** (outbound) would take third-party schemas imported from OpenAPI, with typed ids and typed failures (E6, F2).
- **Queues and caches** don't exist yet. When they are added, they start from delivery semantics in the effect types (3.6), not from a client library.

## Open questions

1. **One schema language or one per system?** A shared core (records, sums, scalars with ranges) plus per-system extensions (collation, delivery, TTL), or separate languages with mappings between them?
2. **How much is proved, and how much is decided?** Many obligations (`fits` for bounded ranges, compatibility) are decidable and can be discharged by `decide`; others (collation correspondence) need a model of the external system's equality. Which external semantics do we model, and to what depth?
3. **Where imported schemas live and how drift is reviewed:** snapshot files next to lock files, a CI job per external system, and a policy for a detected drift (fail the build, or open a change).
4. **Evolution across services we don't control:** a third party changing its API can only be detected, not prevented. What is the runtime posture: strict decoding with typed failures, or tolerant reading with a recorded report?
5. **Where to start.** The two gaps already present in this repository are A1 (JavaScript id precision) and D10 (stored receipts across API versions). A small first step would be the JavaScript-client schema and `fits` for LeanAPI's JSON codecs, together with a compatibility check between the current and next response formats.
