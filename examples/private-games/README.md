# private-games

The worked example from DESIGN.md §9: private tic-tac-toe games that only
their two players can see, with proofs that **no route leaks another
player's games** and that **retries are idempotent**. The exact claims are in
[EVIDENCE.md](../../EVIDENCE.md).

## Layout

| Directory | What |
|---|---|
| `PrivateGames/Domain` | Values, game state, `Valid` / `Allowed` / `Transition`, decisions, domain proofs. No HTTP, no SQL |
| `PrivateGames/Spike` | M3 execution-model spike: pure core + shell vs an effect language (decision 0005) |
| `PrivateGames/Storage` | LeanDB mapping, codec round-trip proofs, the scoped repository, single-writer runtime |
| `PrivateGames/App` | `Core.lean`: routes, decoding, the pure decision (shared with the model). `Service.lean`: the native service |
| `PrivateGames/Model` | Reference model `step`, isolation, existence privacy, idempotence theorems |

## Run

```bash
lake build games
./.lake/build/bin/games --port 8080 --db games.sqlite
./examples/private-games/seed.sh http://127.0.0.1:8080
```

## API

| Route | Notes |
|---|---|
| `POST /players` `{"name","password"}` | Register (unproved route) |
| `POST /sessions` with Basic auth | Returns `{"token","player"}` (unproved route) |
| `POST /games` `{"opponent","minutes"?}` | `Idempotency-Key` optional; 201 with `Location` and `ETag` |
| `GET /games?page&per` | Your games only; `total` counts your games only |
| `GET /games/{id}` | 404 for games you are not in, identical to a missing id |
| `POST /games/{id}/moves` `{"cell":0-8}` | `If-Match: "<rev>"` required (428); stale → 412; `Idempotency-Key` optional |
| `POST /games/{id}/resignation` | Resigning twice is 200 with the same game |

Replayed responses carry `Idempotent-Replayed: true`. Reusing a key with a
different request is 422.

## Docker

Build context is the parent directory of `leanapi` and `leancrypto`:

```bash
docker build -f leanapi/examples/private-games/Dockerfile -t private-games .
docker run -p 8080:8080 -v games:/data private-games
```
