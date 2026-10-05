#!/usr/bin/env bash
set -euo pipefail
# The caller prepares a native integration Lake workspace. All developer paths
# stay in ignored build configuration, never a checked-in release manifest.
workspace=${1:?usage: ddd_check_domain.sh NATIVE_WORKSPACE LEANREACT_REPO}
peer=${2:?usage: ddd_check_domain.sh NATIVE_WORKSPACE LEANREACT_REPO}
root=$PWD
workspace=$(cd "$workspace" && pwd)
# Elan chooses a toolchain from the process directory, before Lake sees -d.
# Run Lake in the workspace so the common graph really uses its qualified pin.
workspace_lake() { (cd "$workspace" && lake "$@"); }
export LEAN_NUM_THREADS=2
workspace_lake build domain_contract_checks
"$workspace/.lake/build/bin/domain_contract_checks"
cp "$peer/engine/LeanContract/Fetch.mjs" .lake/ddd-contract-client/Fetch.mjs
cp "$peer/engine/LeanContract/Codecs.mjs" .lake/ddd-contract-client/Codecs.mjs
DDD_CLIENT_OUT="$PWD/.lake/ddd-contract-client" node --test adapters/domain/tests/client.test.mjs
for fixture in ActorWire ForgedActor ScopeEscape RawPublication QueryWrite; do
  log=".lake/ddd-contract-client/$fixture.log"
  if workspace_lake env lean -j 2 "$root/adapters/domain/tests/negative/$fixture.lean" > "$log" 2>&1; then
    echo "negative fixture unexpectedly compiled: $fixture" >&2
    exit 1
  fi
  if rg -q 'unknown module|bad import|no such file' "$log"; then
    cat "$log" >&2
    exit 1
  fi
  case "$fixture" in
    ActorWire) rg -q 'failed to synthesize.*|Wire' "$log" ;;
    ForgedActor) rg -q 'private|constructor|Invalid.*notation' "$log" ;;
    ScopeEscape|QueryWrite) rg -q 'Type mismatch|type mismatch' "$log" ;;
    RawPublication) rg -q 'Unknown constant|Unknown identifier|unknown constant' "$log" ;;
  esac
  echo "PASS intended compiler rejection: $fixture"
done
proofs=".lake/ddd-contract-client/Proofs.lean"
cat > "$proofs" <<'LEAN'
import LeanApiDomain.Execution
#print axioms LeanApi.Domain.queryFlow_denote
#print axioms LeanApi.Domain.queryFlowWithResources_denote
#print axioms LeanApi.Domain.transaction_abort_restores
LEAN
workspace_lake env lean -j 2 "$root/$proofs" > .lake/ddd-contract-client/proofs.log
python3 - <<'PY'
import re
from pathlib import Path
lines = Path('.lake/ddd-contract-client/proofs.log').read_text()
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
claims = re.findall(r'depends on axioms: \[([^\]]*)\]', lines)
assert len(claims) == 3, lines
for claim in claims:
    assert set(x.strip() for x in claim.split(',') if x.strip()) <= allowed, claim
print('PASS: shared-flow query meaning and native abort kernel proof audit')
PY
