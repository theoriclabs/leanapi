#!/usr/bin/env bash
# Smoke test for the README's starter examples: build them, start each one,
# and check the answers the README shows. Run from anywhere; used in CI.
set -euo pipefail
cd "$(dirname "$0")/../.."
lake build hello items users >/dev/null
BIN=./.lake/build/bin
PID=
stop() { [ -n "$PID" ] && kill "$PID" 2>/dev/null && wait "$PID" 2>/dev/null || true; PID=; }
trap stop EXIT
start() {  # start <exe> <port>
  "$BIN/$1" >/dev/null 2>&1 & PID=$!
  for _ in $(seq 1 50); do curl -s -o /dev/null "http://127.0.0.1:$2/" && return 0; sleep 0.2; done
  echo "FAIL: $1 did not start"; exit 1
}
fails=0
expect() {  # expect <status> <body-substring> <curl args...>
  local want=$1 text=$2; shift 2
  local out status body
  out=$(curl -s -w '\n%{http_code}' "$@"); status=${out##*$'\n'}; body=${out%$'\n'*}
  if [ "$status" = "$want" ] && grep -qF -- "$text" <<<"$body$status"; then echo "  ok   $want $*"
  else echo "  FAIL $* -> $status $body (expected $want, containing '$text')"; fails=$((fails + 1)); fi
}
J=(-H 'content-type: application/json')

echo "hello"
start hello 3000
expect 200 'Hello World!' localhost:3000/
stop

echo "items (path, query and body)"
start items 8000
expect 200 '{"Hello":"World"}' localhost:8000/
expect 200 '{"item_id":5,"q":"somequery"}' "localhost:8000/items/5?q=somequery"
expect 200 '"q":null' localhost:8000/items/5
expect 200 '{"item_id":5,"item_name":"Foo"}' -X PUT localhost:8000/items/5 "${J[@]}" -d '{"name":"Foo","price":42.5}'
expect 422 '"loc":"body.price"' -X PUT localhost:8000/items/5 "${J[@]}" -d '{"name":"Foo"}'
expect 422 '"loc":"path.item_id"' localhost:8000/items/abc
stop

echo "users (middleware, headers and auth)"
start users 3000
expect 200 '[{"id":1,"name":"Ada"}]' "localhost:3000/users?limit=5"
expect 201 '{"id":2,"name":"Grace"}' -X POST localhost:3000/users "${J[@]}" -d '{"name":"Grace"}'
expect 422 '"loc":"body.name"' -X POST localhost:3000/users "${J[@]}" -d '{}'
expect 422 '"loc":"query.limit"' "localhost:3000/users?limit=x"
expect 401 '401' localhost:3000/users/me
expect 200 '"agent":"curl"' localhost:3000/users/me -H 'authorization: Bearer secret' -H 'user-agent: curl'
expect 204 '204' -X OPTIONS localhost:3000/users -H 'origin: http://localhost:5173' -H 'access-control-request-method: POST'
expect 405 '405' -X DELETE localhost:3000/users
stop

if [ "$fails" -ne 0 ]; then echo "starter smoke test FAILED ($fails)"; exit 1; fi
echo "starter smoke test passed"
