#!/usr/bin/env bash
# Seed a running private-games server with two players and one game.
#   ./examples/private-games/seed.sh [http://127.0.0.1:8080]
set -euo pipefail
base=${1:-http://127.0.0.1:8080}
json() { python3 -c "import sys,json; print(json.load(sys.stdin)$1)"; }
for u in alice bob; do
  curl -fsS -X POST "$base/players" -H 'content-type: application/json' \
    -d "{\"name\":\"$u\",\"password\":\"password-$u\"}" >/dev/null || true
done
alice=$(curl -fsS -X POST -u alice:password-alice "$base/sessions" | json '["token"]')
bob_session=$(curl -fsS -X POST -u bob:password-bob "$base/sessions")
bob=$(echo "$bob_session" | json '["token"]')
bob_id=$(echo "$bob_session" | json '["player"]')
game=$(curl -fsS -X POST "$base/games" -H "authorization: Bearer $alice" \
  -H 'content-type: application/json' -H 'idempotency-key: seed-game' \
  -d "{\"opponent\":$bob_id}" | json '["id"]')
echo "ALICE_TOKEN=$alice"
echo "BOB_TOKEN=$bob"
echo "GAME=$game"
echo "try: curl -H \"authorization: Bearer $alice\" $base/games/$game"
