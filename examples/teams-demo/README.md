# Change the schema, and the compiler points at the API

A small users-and-teams API: sign up to a team, see a user on your team, list your team. In four steps, each a real change a product team makes to the schema, the compiler reports what the change means for the API. It reports it in `Api.lean` (or in the file that states the business rule), not in the schema file where the change was made.

```text
./examples/teams-demo/demo.sh status   # the eight steps
./examples/teams-demo/demo.sh next     # apply the next step and show what it does (run it eight times)
./examples/teams-demo/demo.sh reset    # back to the committed app
./examples/teams-demo/demo.sh serve    # serve the app as it is now, for your own curls
./examples/teams-demo/demo.sh check    # the whole demo as a test (CI)
```

Each `next` shows the diff it applies. After a schema change, it runs `lake build` and shows the errors. After the fix, it builds, starts the server on a fresh database, and runs the requests that show the new behaviour. The steps are patches in `beats/`, and `demo.sh check` asserts every error and every HTTP status below, so the demo can't quietly drift from the code.

## The app

- `TeamsDemo/Schema.lean`: tables `TeamRow`, `UserRow` (email, name, team) and `TokenRow`, their keys, and who may see which user: the users on your team (`Policy TeamsDb Me UserRow`).
- `TeamsDemo/Api.lean`: `POST /users` (sign up; the answer carries a token), `GET /users/{id}` and `GET /team`. The two reads go through the policy view, so another team's user is a 404, like a missing one.
- `TeamsDemo/Rules.lean`: the business rule, proved: *you see a user exactly when they are on your team.*

## 1. "Emails must be unique"

```diff
 unique% TokenRow.byDigest := digest
+unique% UserRow.byEmail := email
```
```text
error: examples/teams-demo/TeamsDemo/Api.lean:78:32: Missing cases:
UserRow.Unique.byEmail
```

Sign-up inserts a user and matches every way the insert can fail. The schema now has a way it didn't have before, a clash on email, and the compiler asks what sign-up answers when it happens. The fix is one case, `| .error (.duplicate .byEmail _) => Txn.throw .emailTaken`, and the same email again is now a `409 "that email is taken"`. The answer doesn't reveal the existing account's id.

*In a typical stack,* adding `@unique` compiles, and the first duplicate is a unique-violation exception in production, usually a 500. (If a handler doesn't match the failures and uses LeanDB's default answer instead, a clash is a 409 without any code: either way, never a 500.)

## 2. "Display names are 1 to 64 characters"

```diff
+/-- A display name is 1 to 64 characters. -/
+@[leandb_invariant]
+def UserRow.invariant (u : UserRow) : Bool := 0 < u.name.length && u.name.length ≤ 64
```
```text
error: examples/teams-demo/TeamsDemo/Api.lean:80:45: Application type mismatch: The argument
  trivial
has type
  True
but is expected to have type
  Invariant UserRow row
```

LeanDB stores a row only with evidence that it satisfies the table's rule, and sign-up was passing `trivial`, which is no evidence now. The fix makes the request carry a `DisplayName`, a string with its bound, so an 80-character name is a `422` naming `body.name` when the request is decoded. The row is then `Checked` by proof (`UserRow.checked`). There's no `if` in the handler to forget, and no second copy of "64" to drift.

## 3. "Emails are stored normalized"

```diff
+structure Email where
+  raw : String
+def Email.make (s : String) : Except String Email :=
+  let e := s.trimAscii.toString.toLower
+  if e.contains '@' then .ok ⟨e⟩ else .error "not an email address"
 structure UserRow where
-  email : String
+  email : Email
```
```text
error: examples/teams-demo/TeamsDemo/Api.lean:29:15: Type mismatch
  email
has type
  String
but is expected to have type
  Email
error: examples/teams-demo/TeamsDemo/Api.lean:49:17: Application type mismatch: The argument
  u.val.email
has type
  Email
but is expected to have type
  String
```

Every place a raw string flowed into the column, or out of it into a response, is now an error. The fix decodes an `Email` from the request, so `"  ADA@Acme.com "` and `"ada@acme.com"` are the same address and clash on the unique index from step 1 (`409`), and `"not-an-email"` is a `422` naming `body.email`.

*In a typical stack,* the column stays a string, and a case-insensitive duplicate slips past the unique index until a support ticket finds it.

## 4. "Public profiles are visible to everyone"

```diff
   team : Ref TeamRow
+  isPublic : Bool
 instance : Policy TeamsDb Me UserRow where
-  rule me u := u.val.team == tref me.team
+  rule me u := u.val.team == tref me.team || u.val.isPublic
```
```text
error: examples/teams-demo/TeamsDemo/Rules.lean:23:74: unsolved goals
me : Me
u : Stored UserRow
⊢ u.val.isPublic = true → u.val.team = tref me.team
error: examples/teams-demo/TeamsDemo/Api.lean:30:13: Fields missing: `isPublic`
```

Two layers answer:
- **The API** must decide what a new user's `isPublic` is (the fix: private by default).
- **The business rule no longer holds.** The proof of "you see a user exactly when they are on your team" now has to show that a public profile is on your team, which is false.

The fix restates the rule: *you see a user exactly when they are on your team, or their profile is public* (`sees_iff_same_team_or_public`). A change to who may see what is therefore a visible change to a stated rule, in the diff a reviewer reads.

## What this does not show yet

- **`rule` and `scope` are written separately.** The policy's `rule` (what the proof is about) and its `scope` (the query that becomes SQL) are two copies of the same predicate, and the demo's patches change both. Nothing yet proves they agree; `policy%`, generating both from one lambda, is LeanDB M16.
- **The rule is proved of the policy, not of the running database.** Theorems over the running database need LeanDB M15's laws and its check that execution follows the meaning (DESIGN.md §7.5).
- **Only handlers that match the failures get errors.** The step 1 error appears because sign-up matches the insert's failures. That is the point of typed failures, but a handler that defers to the default answer gets a 409 without a compile error.
