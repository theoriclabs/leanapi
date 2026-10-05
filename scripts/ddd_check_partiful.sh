#!/usr/bin/env bash
# Focused current-source native algebra and private-store/compiler evidence.
set -Eeuo pipefail
# Every failure names its step, line and command (and a negative fixture's log), never silent.
step=setup
trap 'status=$?; echo "FAILED (exit $status) in step [$step], line $LINENO: $BASH_COMMAND" >&2' ERR
workspace=${1:?usage: ddd_check_partiful.sh COMMON_WORKSPACE [NODE_MODULES]}
node_modules=${2:-/Users/harshwork/code/leanreact/node_modules}
root=$PWD
workspace=$(cd "$workspace" && pwd)
export LEAN_NUM_THREADS=2
step=build
(cd "$workspace" && lake build domain_native_command_checks domain_native_read_checks domain_prepared_checks domain_kdf_gate_checks domain_route_checks domain_migration_checks domain_library_app library_browser)
step=route_checks
"$workspace/.lake/build/bin/domain_route_checks"
step=migration_acceptance
node "$root/scripts/ddd_migration_acceptance.mjs" "$workspace"
# Generality fixture: an unrelated library-loans app built from public API only.
step=library_acceptance
node "$root/scripts/ddd_library_acceptance.mjs" "$workspace" --node-modules "$node_modules"
# The post-shaped portable app (LeanReact's PostPart1), when the peer provides it.
step=post_app
post_fixture=0
if rg -q 'lean_exe domain_post_app' "$workspace/lakefile.lean"; then
  post_fixture=1
  (cd "$workspace" && lake build domain_post_app)
  "$workspace/.lake/build/bin/domain_post_app"
  node "$root/scripts/ddd_post_transcript.mjs" "$workspace"
fi
step=native_checks
"$workspace/.lake/build/bin/domain_native_command_checks"
"$workspace/.lake/build/bin/domain_native_read_checks"
"$workspace/.lake/build/bin/domain_prepared_checks"
"$workspace/.lake/build/bin/domain_kdf_gate_checks"
mkdir -p .lake/ddd-partiful-checks
# A negative fixture must fail with exactly the expected message and error count.
expect_rejection() {
  if ! rg -q -- "$1" "$log" || [ "$(rg -c 'error' "$log")" != "$2" ]; then
    echo "FAILED negative fixture $fixture: expected /$1/ and $2 error line(s); its log:" >&2
    cat "$log" >&2
    exit 1
  fi
}
fixtures="UnchangedUnique AuthStoreWire RouteMissingParam RouteGetCommand RouteAppEntry RoutePathCodec"
if [ "$post_fixture" = 1 ]; then fixtures="$fixtures PostApiDuplicate"; fi
for fixture in $fixtures; do
  step="negative:$fixture"
  log=".lake/ddd-partiful-checks/$fixture.log"
  if (cd "$workspace" && lake env lean -j 2 "$root/adapters/domain/tests/negative/$fixture.lean") > "$log" 2>&1; then
    echo "negative fixture unexpectedly compiled: $fixture" >&2
    exit 1
  fi
  if rg -q 'unknown module|bad import|no such file|import .* failed' "$log"; then
    echo "FAILED negative fixture $fixture: it failed for the wrong reason (imports); its log:" >&2
    cat "$log" >&2
    exit 1
  fi
  case "$fixture" in
    UnchangedUnique) expect_rejection 'emailTaken' 1 ;;
    AuthStoreWire) expect_rejection 'failed to synthesize.*|Ontology.Wire' 2 ;;
    RouteMissingParam) expect_rejection 'path parameter :id in "/parties/:id/rsvp" has no matching input field in RouteChecks.rsvp' 1 ;;
    RouteGetCommand) expect_rejection 'GET "/parties/:party/rsvp" requires a query operation, but RouteChecks.rsvp is a command' 1 ;;
    RouteAppEntry) expect_rejection 'RouteAppEntry.lean:25:4: error: path parameter :person in "/people/:person/name" has no matching input field in RouteAppEntry.rename' 1 ;;
    PostApiDuplicate) expect_rejection 'PostApiDuplicate.lean:14:2: error: rsvp is already routed; an operation has one route' 1 ;;
    RoutePathCodec) expect_rejection 'path parameter :password .* RouteChecks.account.signIn input field password : .*Password, which has no LeanApi.Domain.PathParam instance' 1 ;;
  esac
  echo "PASS intended compiler rejection: $fixture"
done
step=axioms
cat > .lake/ddd-partiful-checks/Proofs.lean <<'LEAN'
import LeanApiDomain.Prepared
import LeanApiDomain.Native
import PartifulM1Main
#print axioms LeanApi.Domain.prepared_abort_restores
#print axioms LeanApi.Domain.Native.create
#print axioms LeanApi.Domain.Native.change
#print axioms LeanApi.Domain.Native.project
#print axioms Partiful.app
LEAN
# Milestone 2: `partiful_v2/Main.lean` as staged (`Partiful.Main`).
cat > .lake/ddd-partiful-checks/ProofsV2.lean <<'LEAN'
import Partiful.Main
#print axioms server
#print axioms server.browserApp
LEAN
(cd "$workspace" && lake env lean -j 2 "$root/.lake/ddd-partiful-checks/Proofs.lean") > .lake/ddd-partiful-checks/proofs.log
(cd "$workspace" && lake env lean -j 2 "$root/.lake/ddd-partiful-checks/ProofsV2.lean") >> .lake/ddd-partiful-checks/proofs.log
python3 - <<'PY'
import re
from pathlib import Path
text = Path('.lake/ddd-partiful-checks/proofs.log').read_text()
lines = [line for line in text.splitlines() if 'axioms' in line]
assert len(lines) == 7, text
allowed = {'propext','Classical.choice','Quot.sound'}
for line in lines:
    if 'does not depend on any axioms' in line:
        continue
    match = re.search(r'depends on axioms: \[([^\]]*)\]',line)
    assert match, line
    assert {word.strip() for word in match[1].split(',') if word.strip()} <= allowed, line
print('PASS: native algebra/app definition and DB-owned rollback standard kernel audit')
PY
