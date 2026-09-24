#!/usr/bin/env bash
# The schema-change demo: change the schema, and the compiler points at the API.
#
#   demo.sh next     apply the next step (a schema change, or its fix) and show what it does
#   demo.sh reset    undo every applied step (back to the committed app)
#   demo.sh status   list the steps and mark the next one
#   demo.sh serve    build the app as it is now and serve it on :${DEMO_PORT:-8080}
#   demo.sh check    run every step, asserting each break fails with the expected
#                    error and each fix builds and answers as expected; then reset (CI)
#
# Steps are patches in beats/<beat>/{break,fix}.patch; beats/<beat>/expect lists
# text the failing build must contain. Applied steps are counted in .demo-step.
set -euo pipefail
cd "$(dirname "$0")/../.."
DEMO=examples/teams-demo
STATE=$DEMO/.demo-step
STEPS=(1-unique-email/break 1-unique-email/fix
       2-display-name/break 2-display-name/fix
       3-normalized-email/break 3-normalized-email/fix
       4-public-profiles/break 4-public-profiles/fix)
PORT=${DEMO_PORT:-18123}
CHECK=0

if [ -t 1 ]; then B=$'\e[1m'; G=$'\e[32m'; R=$'\e[31m'; D=$'\e[2m'; X=$'\e[0m'; else B= G= R= D= X=; fi
say()  { printf '%s\n' "$*"; }
head1() { printf '\n%s== %s ==%s\n' "$B" "$*" "$X"; }
fail() { printf '%sFAIL: %s%s\n' "$R" "$*" "$X" >&2; exit 1; }

applied() { [ -f "$STATE" ] && cat "$STATE" || echo 0; }
title() {  # title <step>: line 1 for break, line 2 for fix
  local beat=${1%/*} kind=${1#*/}
  if [ "$kind" = break ]; then sed -n 1p "$DEMO/beats/$beat/title"; else sed -n 2p "$DEMO/beats/$beat/title"; fi
}
show_patch() {  # coloured diff, headers dropped
  sed -e '/^diff --git/d' -e '/^--- /d' \
      -e "s|^+++ b/$DEMO/||" \
      -e "s/^+.*/$G&$X/" -e "s/^-.*/$R&$X/" -e "s/^@@.*/$D&$X/" "$1"
}

build() { lake build TeamsDemo teamsdemo 2>&1; }
errors_of() {  # the error lines of a build, without Lake's trace noise
  grep -E '^error: [a-z]' -A12 | grep -vE '^(trace:|warning:|✖|⚠|Some required|- TeamsDemo|error: (Lean exited|build failed))' |
    sed -e "s|$PWD/||g" -e $'s/\xcc\xb2//g' | awk 'NF || prev {print} {prev=NF}' | head -40
}

# ---- the running app -------------------------------------------------------

SERVER_PID=
DBDIR=
start_server() {
  DBDIR=$(mktemp -d)
  ./.lake/build/bin/teamsdemo --port "$PORT" --db "$DBDIR/teams.sqlite" >"$DBDIR/server.log" 2>&1 &
  SERVER_PID=$!
  for _ in $(seq 1 50); do curl -s -o /dev/null "http://127.0.0.1:$PORT/team" && return 0; sleep 0.2; done
  cat "$DBDIR/server.log"; fail "server did not start"
}
stop_server() {
  [ -n "$SERVER_PID" ] && kill "$SERVER_PID" 2>/dev/null && wait "$SERVER_PID" 2>/dev/null || true
  SERVER_PID=
  [ -n "$DBDIR" ] && rm -rf "$DBDIR"; DBDIR=
}
trap stop_server EXIT

BODY=
req() {  # req <expected-status> <method> <path> <token-or-empty> [json]
  local want=$1 method=$2 path=$3 token=$4 json=${5:-} out status
  local args=(-s -w '\n%{http_code}' -X "$method" "http://127.0.0.1:$PORT$path")
  [ -n "$token" ] && args+=(-H "authorization: Bearer $token")
  [ -n "$json" ] && args+=(-H 'content-type: application/json' -d "$json")
  out=$(curl "${args[@]}")
  status=${out##*$'\n'}; BODY=${out%$'\n'*}
  local shown="$method $path${json:+ $json}"
  if [ "$status" = "$want" ]; then printf '  %s→ %s%s %s\n' "$D" "$shown" "$X" "$G$status$X $BODY"
  else printf '  → %s %s(expected %s)%s %s\n' "$shown" "$R$status" "$want" "$X" "$BODY"; [ "$CHECK" = 1 ] && fail "$shown answered $status, expected $want"; fi
}
field() { sed -n "s/.*\"$1\":\"\\{0,1\\}\\([^\",}]*\\).*/\\1/p" <<<"$BODY" | head -1; }

# The requests each beat adds; after the fix of beat k, beats 0..k all run.
scenario() {
  case $1 in
    0) say "${B}Sign up Ada (Acme) and Gina (Globex); Ada sees her team, not Gina.${X}"
       req 201 POST /users "" '{"email":"ada@acme.com","name":"Ada","team":1}'
       ADA=$(field token)
       req 201 POST /users "" '{"email":"gina@globex.com","name":"Gina","team":2}'
       GINA_ID=$(sed -n 's/.*"user":{[^}]*"id":\([0-9]*\).*/\1/p' <<<"$BODY")
       req 200 GET /team "$ADA"
       req 404 GET "/users/$GINA_ID" "$ADA"
       req 422 POST /users "" '{"email":"x@y.com","name":"X","team":9}' ;;
    1) say "${B}The same email again:${X}"
       req 409 POST /users "" '{"email":"ada@acme.com","name":"Ada 2","team":1}' ;;
    2) say "${B}A display name that is too long, or empty:${X}"
       req 422 POST /users "" "{\"email\":\"long@acme.com\",\"name\":\"$(printf 'x%.0s' $(seq 1 80))\",\"team\":1}"
       req 422 POST /users "" '{"email":"empty@acme.com","name":"","team":1}' ;;
    3) say "${B}The same email with other capitals and spaces, and a malformed one:${X}"
       req 409 POST /users "" '{"email":"  ADA@Acme.com ","name":"Ada 3","team":1}'
       req 422 POST /users "" '{"email":"not-an-email","name":"N","team":1}' ;;
    4) say "${B}New users are private, so Gina is still invisible to Ada:${X}"
       req 404 GET "/users/$GINA_ID" "$ADA" ;;
  esac
}
run_scenarios() {  # run_scenarios <last-beat> <show-only-last?>
  start_server
  local k
  for k in $(seq 0 "$1"); do
    if [ "$2" = yes ] && [ "$k" -lt "$1" ]; then
      scenario "$k" >/dev/null
      [ "$k" = 0 ] && say "${D}(setup: Ada signs up to Acme, Gina to Globex)${X}"
    else scenario "$k"; fi
  done
  stop_server
}

# ---- steps -------------------------------------------------------------------

do_step() {  # do_step <index>
  local step=${STEPS[$1]} beat kind
  beat=${step%/*}; kind=${step#*/}
  head1 "Step $(( $1 + 1 ))/${#STEPS[@]}: $(title "$step")"
  show_patch "$DEMO/beats/$step.patch"
  git apply "$DEMO/beats/$step.patch"
  echo $(( $1 + 1 )) > "$STATE"
  local out
  if [ "$kind" = break ]; then
    say ""; say "${B}\$ lake build${X}"
    if out=$(build); then fail "the build passed; this change should break the API"; fi
    printf '%s\n' "$out" | errors_of
    local missing=0 line
    while IFS= read -r line; do
      [ -z "$line" ] && continue
      grep -qF -- "$line" <<<"$out" || { say "${R}expected in the build output: $line${X}"; missing=1; }
    done <"$DEMO/beats/$beat/expect"
    [ "$missing" = 0 ] || fail "the build failed, but not as expected"
    say "${R}✗ build fails${X}  ${D}(next: the fix)${X}"
  else
    say ""; say "${B}\$ lake build${X}"
    out=$(build) || { printf '%s\n' "$out" | errors_of; fail "the fix does not build"; }
    say "${G}✓ build passes${X}"
    say ""
    run_scenarios "${beat%%-*}" yes
  fi
}

reset_all() {
  local n i; n=$(applied)
  for ((i = n - 1; i >= 0; i--)); do git apply -R "$DEMO/beats/${STEPS[$i]}.patch"; done
  rm -f "$STATE"
}

case ${1:-status} in
  next)
    n=$(applied)
    [ "$n" -lt "${#STEPS[@]}" ] || { say "All steps are applied. Run: $0 reset"; exit 0; }
    do_step "$n" ;;
  reset)
    reset_all; say "Back to the committed app." ;;
  status)
    n=$(applied)
    for i in "${!STEPS[@]}"; do
      mark="  "; [ "$i" = "$n" ] && mark="▸ "
      printf '%s%d. %s\n' "$mark" $(( i + 1 )) "$(title "${STEPS[$i]}")"
    done
    [ "$n" -ge "${#STEPS[@]}" ] && say "(all applied; $0 reset to start over)" || true ;;
  serve)
    build >/dev/null || fail "the app does not build in this state"
    DB=$(mktemp -d)/teams.sqlite
    say "Serving on http://127.0.0.1:${DEMO_PORT:-8080} (fresh database $DB). Ctrl-C to stop."
    exec ./.lake/build/bin/teamsdemo --port "${DEMO_PORT:-8080}" --db "$DB" ;;
  check)
    CHECK=1
    [ "$(applied)" = 0 ] || fail "steps are applied; run $0 reset first"
    trap 'stop_server; reset_all' EXIT
    head1 "Step 0: the app as committed"
    build >/dev/null || fail "the committed app does not build"
    run_scenarios 0 no
    for i in "${!STEPS[@]}"; do do_step "$i"; done
    reset_all
    say ""; say "${G}demo check passed: every break fails as expected, every fix builds and answers as expected${X}" ;;
  *)
    sed -n '2,11p' "$0"; exit 2 ;;
esac
