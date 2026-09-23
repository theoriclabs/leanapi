# 0005. Execution model: pure decisions in a thin shell over a scoped repository (Q1)

Status: accepted (provisional), M3, 2026-09-22. Confirmed or revised in M6.

## Spike

`examples/private-games/PrivateGames/Spike/` implements `PlayMove` and
`ListMyGames` both ways. Each version has a pagination query, an
external-effect intent (a "game ended" notification) and one custom theorem.

| | (a) `Shell.lean`: pure `decide` + effectful shell | (b) `Effects.lean`: `Prog` free monad + interpreter |
|---|---|---|
| Handler code | Ordinary `do` over a `Repo m` record | `do` over `Prog`, a fixed set of constructors |
| Custom theorem tried | `playMoveCore_participant`: a successful core yields a game the caller participates in, whatever was loaded. Proof: 10 lines, through the domain lemma | `reads_visible`: for **every** program, every game it reads is visible to the actor. Proof: induction on `Prog`, about 25 lines |
| What "all code paths" covers | The pure core of each operation (all branches). The shell is reviewed, not proved | Every program that can be written, since there is no ambient `IO` |
| Pagination | `listVisible p off lim` in the repo. `listMine_visible` proved over the in-memory repo | `Prog.list`. Covered by `reads_visible` |
| Effect intents | Pure function `endIntent before after` returns intents. The shell enqueues them after commit | `Prog.intent`. The interpreter appends to the outbox |
| Proving through monadic shell code | Painful: a first attempt at a theorem over `StateM` shell code was abandoned (split/simp on bind chains). Moving the logic into a pure core fixed it | Natural: the interpreter is a structural recursion |
| Escape hatch | Plain `IO` handlers stay possible. They are outside the proved set and reported as such | Adding `liftIO` would void `reads_visible`, so every new capability is a new constructor plus a proof update |
| Native execution | The shell runs on LeanDB directly | Needs an interpreter per backend, and its refinement to LeanDB is another obligation |

## Decision

Candidate **(a)**, with the key property of (b) kept by construction:

1. Each proved operation is a **pure core**: `load result → decision →
   (commit plan, response)`. The core calls the domain's `decide` functions
   (`playMove`, `resign`, `openGame`).
2. The **only** data access a proved operation gets is a scoped repository
   whose read functions take the actor and conjoin the visibility policy
   into the query (M4). The raw connection is not exported to proved
   operations.
3. The **shell** (load via the repository, run the core, commit against the
   revision, record the receipt, enqueue intents) is framework code, the same
   for every operation. It is small, so it is reviewed and tested
   differentially against a model. M6 proves properties of a **reference
   model** that calls the same pure cores; the native shell is trusted to
   refine it, and the differential tests are the evidence for that.
4. Plain `IO` handlers (M1 routes) remain available. They sit outside the
   proved set, and M7 reports them at build time.

"All code paths" therefore means: every branch of every proved operation's
core, the model's routing, decoding, authentication and commit steps, and
the scoped repository's model. Middleware (decision 0001), the native
shell/LeanDB refinement and the authenticator remain assumptions.

## Why not (b) now

(b) gives the strongest statement, but it makes every handler a continuation
program, needs an interpreter per backend (plus a refinement proof for each),
and turns every new capability into a language change. Keep it as a later
option for high-assurance operations: the scoped-repository contract in (a) is
exactly `Prog`'s constructor set, so migrating later means writing an
interpreter, not rewriting the domain.
