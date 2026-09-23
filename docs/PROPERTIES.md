# Property library: plug-in properties, their shapes, and admissibility

Status: design, 2026-09-23; implemented as `LeanApi.Props` in 0.6.0 (PLAN.md M8–M12). Code blocks are sketches of shape; the compiled APIs are in `LeanApi/Props/`. Where the implementation differs: `@[leandb_invariant]` became `StoredInvariant` (decision 0017), `#check_admissible` is `#check_invariant` plus the registry, and `Keyed` scopes keys by a function of the request. The open questions in §8 are settled by decisions 0016–0019.

The goal: an application author should be able to pick a property from a library ("this route is idempotent", "games' move logs only grow", "no player observes another player's games"), attach it to their system, and get back one of three things:

1. a proof, because the property follows from what the system already declares;
2. a short, precise list of obligations still to discharge;
3. a diagnosis that the property is ill-formed, vacuous, or not admissible as stated, with what would fix it.

The approach depends on something specific to Lean: a property is a typed value. It has a **shape** (which states, runs and observations it talks about), and the shape determines how it can be proved, how it composes with other properties, and what makes it meaningful.

---

## 1. Where we are today

At `861e93e`, plus the 2026-09-23 review follow-up:

| Property | Generic (library) or app-specific | Where |
|---|---|---|
| Response noninterference (isolation) | **Generic**: `ScopedApp` with `Obligations` / `CallerObligations`; apps prove three obligations and get the theorem | `LeanApi/Proofs/Scoped.lean` |
| Unrouted requests don't change the world | **Generic** | `ScopedApp.unrouted_pure` |
| Middleware stage transparency | **Generic** for the typed stage forms | `LeanApi/Http/Typed.lean` (`decorate_preserves`, `guard_transparent`, `guard_observes`) |
| Keyed idempotence (replay returns receipt) | App-specific, for private-games | `PrivateGames/Model/Idempotence.lean` (`keyed_replay`) |
| Safe reads (GET doesn't change the world) | App-specific | `reads_pure` |
| Invariant preservation, `Allowed`, `Transition` | App-specific | `PrivateGames/Domain/Proofs.lean` |
| Availability (owner can read) | App-specific | `read_available` |

So one property (isolation) is plug-and-play today. Its earlier all-observer form was near-vacuous (review C1, [review of 861e93e](reviews/2026-09-22-review-861e93e.md)); the caller-specific form fixes the claim. That is the motivating failure for §5: a property can type-check and be proved while saying nothing. A library has to catch that.

---

## 2. The system signature everything is stated against

Every library property is stated against one abstract signature. An app instantiates it once. Today's `ScopedApp` is a richer, pipeline-specific instance of it.

```lean
structure Sys where
  World  : Type
  Req    : Type
  Res    : Type
  Env    : Type                         -- time, randomness, config: the "Facts" of DESIGN §2.3
  step   : Env → Req → World → Res × World
  init   : World → Prop                 -- admissible initial worlds
```

Everything a property may mention must be reachable from this signature, or from named projections the app declares on it:

```lean
structure Observation (S : Sys) where
  Observer : Type
  obs      : Observer → S.Res → Obs        -- what an observer sees of a response
  view     : Observer → S.World → View     -- what an observer may see of a world
```

Declaring `view` as a **function** (a projection), rather than as an arbitrary relation, is the first well-formedness rule. `SameView a w₁ w₂` is then defined as `view a w₁ = view a w₂`, so it is an equivalence by construction. An arbitrary relation can silently be equality, which is what made review finding C1 possible.

---

## 3. Shapes

A property's shape is how many worlds, runs and steps it relates. The shape decides the proof method, the composition rules, and the admissibility conditions.

| Shape | Relates | Examples | Proof method |
|---|---|---|---|
| **State invariant** | one world | "every stored game is `Valid`", "revisions are unique" | Induction over reachable worlds: holds initially, preserved by every step |
| **Step property** (pre/post) | one step: `w, req, res, w'` | "GET leaves the world unchanged", "move log only grows", "revision increases by one on commit" | Per-route case analysis |
| **Two-step, same run** | `step r (step r w).2` vs `step r w` | idempotence, "second resign is a no-op" | Per-route: the first step's post-state satisfies the second step's no-op precondition |
| **Two-run (relational)** | two runs from related worlds | noninterference, determinism, existence privacy | Unwinding: a relation on worlds preserved by every step and fixing the observation |
| **Trace (safety)** | a sequence of steps | "a revoked token is never accepted again", "each key commits at most once" | Reduce to a state invariant over a history-augmented world |
| **Enabledness** | one world, existence of a successful step | availability: "a participant can read their game" | Constructive: exhibit the request and show the success branch is taken |
| **Commutation** | two different requests in either order | "moves on different games commute" (concurrency) | Per pair of routes: both orders yield equal results |

Liveness ("eventually delivered") is out of scope for the first library. It is not a step-level shape.

In Lean, the shape is an index, so the library knows which method and which composition rules apply:

```lean
inductive Shape | inv | stepProp | twoStep | relational | trace | enabled | commute

structure Property (S : Sys) where
  shape : Shape
  holds : Prop
```

The library's value is in the *constructors*. Each one builds a `Property` of a known shape from small, app-supplied pieces, and comes with a theorem saying which obligations suffice.

---

## 4. The library: property constructors with proof principles

Each entry has three parts: what the app supplies, what it must prove, and what it gets.

### 4.1 Invariant

```lean
def Invariant (S : Sys) (I : S.World → Prop) : Property S :=
  ⟨.inv, ∀ w, Reachable S w → I w⟩

structure Inductive (S : Sys) (I : S.World → Prop) : Prop where
  init  : ∀ w, S.init w → I w
  step  : ∀ e r w, I w → I (S.step e r w).2

theorem Invariant.of_inductive : Inductive S I → (Invariant S I).holds
```

**App supplies** `I`. **Obligations:** `Inductive S I`. **Per-route form:** if the route table is a finite list, `step` splits into one obligation per route. A new route adds an obligation (DESIGN P6).

### 4.2 Safe route (no mutation)

```lean
def Safe (S : Sys) (sel : S.Req → Prop) : Property S :=
  ⟨.stepProp, ∀ e r w, sel r → (S.step e r w).2 = w⟩
```

**Discharged automatically** when the route's handler has no write operations (DESIGN §4.3). That is decidable by inspecting the operation's plan type, so the library can prove it with no user input.

### 4.3 Idempotence (three variants)

```lean
-- (a) state idempotence under a fixed environment
def IdemState (S : Sys) (sel : S.Req → Prop) : Property S :=
  ⟨.twoStep, ∀ e r w, sel r →
      (S.step e r (S.step e r w).2).2 = (S.step e r w).2⟩

-- (b) plus response equivalence modulo a declared relation
def Idem (S : Sys) (sel : S.Req → Prop) (≈ : S.Res → S.Res → Prop) : Property S := ...

-- (c) keyed: any operation becomes idempotent under a receipt ledger
def Keyed (S : Sys) : Sys   -- system transformer: adds receipts to World, keys to Req
theorem keyed_idem : LedgerLaws S → (Idem (Keyed S) hasKey replayEquiv).holds
```

**Plug and play:**

- **(c) is the main library theorem.** Wrap any system in the `Keyed` transformer and prove `LedgerLaws` once for the ledger implementation (it records atomically, lookup finds what was recorded, keys are scoped by actor and operation, and a fingerprint mismatch is rejected). Every route is then idempotent under a key, for free. Today `keyed_replay` proves this for private-games alone, and only for the replay immediately after the commit. A library version should hold for a replay after any interleaving that doesn't remove the receipt. That is a trace-shaped strengthening, discussed in §6.3.
- **(a) is derivable from the domain** when the operation is a decider (DESIGN §2.3):

  ```lean
  theorem idem_of_decider :
    (∀ a s c es, decide a s c = .ok es → decide a (es.foldl evolve s) c = .ok []) →
    (IdemState (fromDecider ...) (isCmd c)).holds
  ```

  The app proves a fact about pure `decide`/`evolve`; the library lifts it through load, commit and respond.

### 4.4 Noninterference (per observer)

```lean
def NI (S : Sys) (O : Observation S) : Property S :=
  ⟨.relational, ∀ a e r w₁ w₂,
      O.view a w₁ = O.view a w₂ → AuthAs r w₁ a →
      O.obs a (S.step e r w₁).1 = O.obs a (S.step e r w₂).1⟩

def NIUnwinding (S : Sys) (O : Observation S) : Property S :=   -- adds the successor clause
  ⟨.relational, ∀ a e r w₁ w₂, O.view a w₁ = O.view a w₂ →
      O.view a (S.step e r w₁).2 = O.view a (S.step e r w₂).2 ∧ ...⟩
```

This is today's `ScopedApp.CallerObligations` theorem, restated over a projection. The unwinding form is what extends to traces (§6.2).

### 4.5 Enabledness (the positive twin)

```lean
def Enabled (S : Sys) (pre : S.World → S.Req → Prop) (ok : S.Res → Prop) : Property S :=
  ⟨.enabled, ∀ e w r, pre w r → ok (S.step e r w).1⟩
```

The library **pairs** every restrictive property with an enabledness property, so that "deny everything" can't satisfy the package (DESIGN §2.4). For example, `NI` for games comes with `Enabled (participant reads own game) (status = 200)`.

### 4.6 Other constructors worth having early

| Constructor | Shape | Typical use |
|---|---|---|
| `Monotone (f : World → α) (≤)` | step | move logs only grow; revisions only increase |
| `Frame (sel) (untouched : World → β)` | step | "moves on game g don't change other games" |
| `Unique (key : Row → K)` | invariant | usernames unique; one receipt per (actor, op, key) |
| `AtMostOnce (event)` | trace | each key commits at most once |
| `Commutes (sel₁ sel₂)` | commute | independent aggregates can run concurrently |
| `Refines (native model)` | relational, across systems | the native server matches the model on outputs (DESIGN §8.4) |

---

## 5. Well-formed, non-vacuous, admissible

These are three distinct gates. A property should pass all three before its proof is treated as evidence.

### 5.1 Well-formed: the statement means what its shape says

Checked mostly by types:

| Rule | Why | How it is enforced |
|---|---|---|
| Mentions only declared projections (`view`, `obs`, route selectors), never raw internals | Otherwise the property depends on representation, and refactors silently change its meaning | The constructors take projections, not worlds |
| Observer relations are equivalences | NI over a non-reflexive relation is meaningless; over a non-transitive one it doesn't compose | Relations are induced by projections: `view a w₁ = view a w₂` |
| Relational properties are per observer | "∀ observers agree" is almost always equality of worlds (review C1) | `NI` is indexed by one observer; the all-observers form is not a library constructor |
| Environment inputs are explicit | Idempotence or NI that implicitly depends on time or randomness is false or vacuous | `step` takes `Env`; two-step and relational properties quantify over a *shared* `e` |
| The request selector is decidable and total over the route table | So coverage ("every route has a proof") can be computed | `sel` built from route ids |

### 5.2 Non-vacuous: the property can actually fail

A proved property is vacuous if its hypotheses are unsatisfiable, or so strong that the conclusion is trivial. The library asks for small witnesses alongside the proof:

| Shape | Vacuity risk | Witness the library asks for |
|---|---|---|
| Invariant | `I` is `True`, or no world is reachable | `∃ w, S.init w`, and a world violating `I` (so `I` rules something out) |
| Relational (NI) | `view a` is injective, so equal views means equal worlds | **Hiddenness witness:** `∃ w₁ w₂, view a w₁ = view a w₂ ∧ w₁ ≠ w₂`, ideally differing in another actor's data. This check would have caught review finding C1 immediately |
| Two-step (idempotence) | The selector matches no request, or the first step always fails | A request and world where the first step commits |
| Any restrictive property | Satisfied by rejecting everything | The paired `Enabled` property (§4.5) |
| Anything with hypotheses | Hypotheses are contradictory | `∃` an instance satisfying them all |

These witnesses are cheap. Most are concrete `example`s checked by `decide` or `rfl` on small worlds. A random search (Plausible) can suggest them before anyone writes a proof.

### 5.3 Admissible: the library's proof principle applies

A well-formed, non-vacuous property can still be true but out of reach of the constructor's proof method. Admissibility conditions are the side conditions each method needs. When one fails, the library should say which, and what would fix it:

| Property | Admissibility condition | If it fails | What makes it admissible |
|---|---|---|---|
| Invariant `I` | `I` is inductive | Some step from a reachable-but-weird world breaks `I`, although no reachable world does | **Strengthen:** supply `J ⊆ I` that is inductive (for example, add "revisions are unique" to make "at most one row per game" inductive). Or prove `I` relative to an already-proved invariant (`Inductive S (J ∧ I)` given `J`) |
| `IdemState` | Step is deterministic given `Env`; `Env` is shared between the two steps | Time-dependent handlers (clocks, expiry) give different results on replay | Move time into `Env` and quantify over equal `Env`; or state idempotence only for time-independent routes; or use keyed idempotence, whose replay does not re-run the handler |
| `IdemState` | Second application meets the no-op precondition | "Delete, then delete again" returns 404 the second time | Weaken to `Idem` with a declared response equivalence (`≈` treats 204 and 404 as equivalent); or use keyed idempotence |
| `Keyed` idempotence | Ledger write is atomic with the state change; key scope includes actor and operation; fingerprint covers the whole input | A key reused across users or operations replays someone else's response | Prove `LedgerLaws`; the library's `Keyed` transformer fixes the key scope, so the app cannot choose it wrongly |
| `NI` (single step) | Authentication depends only on the caller's view (their session); load depends only on the caller's view | Auth that reads a global table (for example "is the user banned?") leaks through its response | **Enlarge the view** to include the facts auth reads; or make them public (every observer's view includes them) |
| `NIUnwinding` / trace NI | Every step by *any* actor preserves view-equivalence for observer `a` | Another actor's write changes `a`'s view differently in the two worlds (for example, shared counters) | Include the shared data in `a`'s view (it's observable anyway); or prove the write's effect on `a`'s view is a function of `a`'s view |
| `Commutes` | The routes touch disjoint parts of the world (a frame condition) | Two moves on the same game | Restrict the selector to different aggregates; that is exactly the aggregate-as-concurrency-boundary rule in DESIGN |
| `Refines` for relational properties | The model is deterministic, and the native server matches it on outputs | Ordinary refinement does not preserve hyperproperties: a nondeterministic model can be refined by a leaky implementation | Keep the model deterministic (it is today), and state refinement as output equality, not trace inclusion |

The last row matters for evidence: safety properties transfer from model to native by simulation, but noninterference transfers only because the model is deterministic. That is a design constraint on the reference model, and should be written into it.

### 5.4 Making Lean report what is missing

Lean can produce the "what would make this admissible" answer mechanically. Admissibility conditions become type classes, and constructors require them as instances:

```lean
class Deterministic (S : Sys) : Prop
class EnvFree (S : Sys) (sel : S.Req → Prop) : Prop      -- step ignores Env on these routes
class ViewClosed (S : Sys) (O : Observation S) : Prop     -- unwinding condition

def IdemState.prove [Deterministic S] [EnvFree S sel] (h : NoOpAfter S sel) : (IdemState S sel).holds
```

A missing instance then surfaces as an elaboration error naming the missing condition. A custom `#check_admissible` command could list all of them at once, with the remedies from §5.3 as attached documentation. Instances derivable by construction (for example `Safe` for plan types without writes) are provided by the library, so the author only sees conditions that genuinely need thought.

---

## 6. An algebra of invariants

This section is about invariants in general, not any particular property. It asks three things of any combination of invariants: is the result well-formed, is it admissible (provable by induction), and if not, what exactly is missing.

### 6.1 Every safety shape is an invariant of a derived system

The shapes in §3 look different, but every safety shape is a state invariant of some system derived from `S`:

| Shape | Derived system | The property becomes |
|---|---|---|
| State invariant | `S` itself | `I : S.World → Prop` |
| Step property `P w r w'` | `S` with the last transition recorded in the state | an invariant over (previous world, request, world) |
| Trace safety ("a revoked token is never accepted again") | `S` with a history variable, or `S` × a monitor automaton | an invariant of the augmented world |
| k-run relational (noninterference, determinism) | self-composition `Sᵏ`: k copies run on the same requests and environment | an invariant relating the k worlds (for noninterference, "views agree" plus "outputs agree") |
| Two-step same run (idempotence) | sequential self-composition: a run and its replay | an invariant of the pair |

So a **shape is a system constructor** `σ : Sys → Sys`, and a property of shape σ is an invariant of `σ S`. That makes composition uniform:

- **Same shape:** combine as invariants of one system (§6.3).
- **Different shapes:** embed both into a common derived system and combine there. For example, a state invariant `I` becomes the relational invariant `I w₁ ∧ I w₂` on `S²`. A trace invariant and a relational one meet on the self-composition of the history-augmented system. The embeddings are projections, so this is pullback (§6.3).

It also means there is one proof principle, induction over the derived system. Every admissibility question becomes "is this invariant inductive for that system, and if not, what is missing?"

### 6.2 Invariants as types, admissibility as a restricted step

In Lean, an invariant has a direct type-level reading:

- A **well-formed** invariant `I` gives a subtype `{w // I w}`: the worlds it admits.
- An invariant is **inductive** exactly when the step restricts to that subtype:

  ```lean
  def Inductive.restrict (h : Inductive S I) : Sys :=
    { S with World := {w // I w}, step := fun e r w => let (res, w') := S.step e r w.1; (res, ⟨w', h.step e r w.1 w.2⟩) }
  ```

  If the step can't be written with that type, the invariant isn't admissible. The type error sits in the proof obligation `h.step`.
- **Composing invariants** is then composing subsystems. Conjunction is the intersection of subsystems, and pullback is restriction along a map.

This is the sense in which invariants have a shape one can compute with. The library operates on these subsystems, not on bare `Prop`s.

### 6.3 Operators, when they preserve admissibility, and the residual obligation

`Ind(I)` means `I` is inductive. The last column is what the library asks for when the rule doesn't apply directly.

| Operator | Admissible when | Otherwise, the residual obligation |
|---|---|---|
| **Conjunction** `I ∧ J` | `Ind(I)` and `Ind(J)` | `J` inductive *relative to* `I`: `I w ∧ J w → J (step w)`. With `Ind(I)` this gives `Ind(I ∧ J)`. With a cyclic dependency, prove the cycle's conjunction jointly (mutual induction) |
| **Disjunction** `I ∨ J` | `Ind(I)` and `Ind(J)` (a union of closed sets is closed) | Case analysis per step: each disjunct's successor lands in *some* disjunct. Two non-inductive disjuncts can still make an inductive disjunction |
| **Indexed conjunction** `∀ i, I i` (per game, per user) | each `Ind(I i)` | **Locality:** if a step touches only entity `i` (a *frame* condition), the obligation splits into "the step preserves `I i`" plus "the step leaves every `j ≠ i` unchanged". Without a frame lemma, every step must be checked against every index |
| **Indexed disjunction** `∃ i, I i` | each `Ind(I i)` | As for disjunction |
| **Implication** `I → J`, **negation** `¬ I` | Not preserved in general | Restate. "If a game is finished, it has no pending draw offer" becomes `J` relative to `I`. "Once revoked, stays revoked" is a step property (monotonicity), so move it to the step-augmented system |
| **Pullback** `I ∘ f` along `f : S.World → T.World` (an abstraction, a projection, or a shape embedding) | `Ind_T(I)` and `f` is a simulation: `f (S.step e r w).2 = (T.step e' r' (f w)).2` for corresponding inputs | Prove the commuting square. If `S` takes internal steps `T` doesn't have (stuttering), `I` must be closed under `T`'s reflexive step, or the internal steps must leave `f w` unchanged |
| **Image / pushforward** `f(I)` | Rarely: needs a backward simulation | Usually: state the invariant on the source instead |
| **Product of independent systems** `S₁ × S₂` | `Ind(I₁)` and `Ind(I₂)` | With shared state (bounded contexts over one database): **rely/guarantee**. Each component's steps must preserve the other's invariant. The obligation is "B's writes frame A's state", or an explicit lemma that they preserve `I_A` |
| **Union of transitions** (adding a route, a job, an admin command, a migration) | `Ind(I)` for each transition source | One obligation per new writer. This is the coverage rule in DESIGN §4.3: an unproved writer invalidates every invariant it can touch |
| **Sequential composition inside a transaction** `op₁ ; op₂` | The composite preserves `I` | The intermediate world may violate `I`. That is only sound if no one can observe it, so atomicity becomes an assumption. The invariant is then stated over *stable* (between-transaction) worlds |
| **Refinement** (model → native) | A pullback along the refinement map | As for pullback. Relational invariants additionally need the model to be deterministic, or the output equality stated directly (§5.3) |

### 6.4 Well-formedness of a composite

A composite can be ill-formed even when its parts are fine:

| Condition | What goes wrong | Enforcement or remedy |
|---|---|---|
| **Same carrier** | Conjoining an invariant over `S` with one over `S²` is a type error, not a proof burden | Explicit embedding (pullback along a projection) into a common derived system |
| **Representation independence** | The world stores games in a `List`, but the intended meaning is a set, or ids up to renaming. An invariant that depends on list order is about the encoding, not the domain | Each invariant proves it respects the intended equivalence. `∧`, `∨`, `∀`, `∃` preserve respect; pullback preserves it if `f` respects it. Alternatively, state invariants on a canonical form |
| **Decidability** (for runtime checks, e.g. `@[leandb_invariant]`) | An unbounded `∀` over an infinite domain can't be checked at runtime | `∧`, `∨`, `¬`, and bounded `∀`/`∃` preserve `Decidable`. The library marks which composite invariants have a runtime check derived from the same definition (open question P7) |
| **Joint satisfiability** | `I` and `J` are each satisfiable, yet `I ∧ J` admits no initial world, so everything proved under it is vacuous | A joint witness: `∃ w, S.init w ∧ I w ∧ J w`. Vacuity is not compositional; each composite needs its own witness (§5.2) |
| **Hypothesis creep** | Using a strong proved invariant as a hypothesis for a later property can make that property's premise unsatisfiable | Re-check the later property's witness under the invariants it assumes |

### 6.5 When an invariant isn't admissible: what exactly is needed

"Not inductive" has a precise, canonical diagnosis:

1. **Counterexample to induction (CTI).** A world `w` with `I w` and a request `r` where `¬ I (step r w)`. There are two cases:
   - `w` is reachable. Then `I` is false, and no proof will help.
   - `w` is unreachable. Then `I` needs strengthening to exclude `w`.

   The library can search for CTIs (small worlds, random or exhaustive) before anyone attempts a proof.

2. **The weakest inductive strengthening exists and is canonical.** Define the predicate transformer

   ```lean
   def pre (S : Sys) (X : S.World → Prop) : S.World → Prop := fun w => ∀ e r, X (S.step e r w).2
   ```

   The greatest fixpoint of `X ↦ I ∧ pre S X` is the weakest inductive invariant contained in `I`. It exists by Knaster–Tarski, because `pre` is monotone. Then:

   ```lean
   theorem invariant_iff : Invariant S I ↔ ∀ w, S.init w → WeakestInductive S I w
   ```

   So the question "what is needed to make `I` admissible?" has a definite answer. Any `J` with `init ⊆ J ⊆ WeakestInductive S I` works, and nothing weaker does. In practice the library offers the unfoldings in order:
   - `I`
   - `I ∧ pre I`
   - `I ∧ pre I ∧ pre² I`

   Each is a candidate strengthening (k-induction), and each CTI shows which conjunct is missing.

3. **Worked example, from private-games.** "Game ids are unique" is not inductive by itself. A CTI is a world whose `nextGame` equals an existing game's id: opening a game then creates a duplicate. The CTI names the missing conjunct: `∀ g ∈ w.games, g.id < w.nextGame`. `Unique ∧ Fresh` is inductive, and `Fresh` is inductive on its own. The same pattern gives receipt uniqueness per (actor, op, key).

4. **Missing locality.** When an indexed invariant fails only because a step *might* touch other entities, the residual is a frame lemma for that step, not a stronger invariant.

5. **Dependency order.** Relative invariants form a graph. The library orders it topologically and proves each invariant using earlier ones. A cycle is reported as a set to prove jointly.

### 6.6 Beyond single invariants

Combinations of *different kinds* of property also have rules. Noninterference paired with enabledness says "sees exactly their own data". A keyed replay of a private response interacts with revocation. These combinations reduce to the invariant algebra above via §6.1: both properties become invariants of a common derived system, and the same operators, obligations and diagnoses apply.

---

## 7. What an author's workflow would look like

```lean
-- 1. Declare the system and observation (once per app).
def games : Sys := ...
def gamesObs : Observation games := { view := fun p w => (visibleGames p w, ownReceipts p w, ...), ... }

-- 2. Pick properties.
def props : List (Property games) := [
  Invariant games (fun w => ∀ g ∈ w.games, Valid g),
  NI games gamesObs,
  Enabled games participantRead ok200,
  Idem (Keyed games) hasKey replayEquiv,
  IdemState games (routeIs .resign),
  Safe games isGet ]

-- 3. Ask what's needed.
#check_admissible props
--   Invariant: needs `Inductive`; per-route obligations: openGame, playMove, resign
--   NI: needs `ViewClosed`; hiddenness witness: missing
--   IdemState resign: `EnvFree` ✓, `NoOpAfter` needs proof
--   Safe isGet: discharged (no write plan)
--   Keyed: discharged by library (`LedgerLaws` proved for the LeanDB ledger)
```

Output like this is also the evidence record. `EVIDENCE.md` could be generated from it, so its "proved" column can't claim more than the checked theorems state (review H4).

---

## 8. Open questions

**P1. One signature or several?** `Sys` is small and general, while `ScopedApp` bakes in the pipeline, which makes proofs cheap. The plan is to keep both, with `ScopedApp → Sys` as a lifting, but it is unclear where each property's canonical statement should live.

**P2. Proof automation vs. explicit obligations.** Which obligations can be discharged by `simp`, `decide` or a custom tactic (`route_cases`), and which should always be visible to the author?

**P3. Vacuity checks as proofs or as tests?** Hiddenness witnesses can be proved (an `∃`) or searched for (Plausible). A proved witness is stronger, while a search is cheaper and finds counterexamples to the property itself.

**P4. Trace properties and time.** Expiry, revocation and retention windows need `Env` to carry time across steps. How much temporal structure should the library encode before it becomes a model checker?

**P5. Declassification.** Existence privacy says hidden and missing look the same. Some apps deliberately release information (a username is taken, a count is public). NI needs a principled way to state allowed releases without making the property vacuous.

**P6. Where do app-specific properties go?** Should an app's own properties (a move log only grows, stock never goes negative) use the same constructors, and get the same admissibility checks, as library ones? The design above says yes. The cost is that every property needs a shape.

**P7. Relationship to LeanDB.** Invariants over stored rows could be checked by LeanDB at runtime (`@[leandb_invariant]`) and proved in the model. The open question is whether the library should generate the runtime check from the proved `I`, so the two cannot drift.
