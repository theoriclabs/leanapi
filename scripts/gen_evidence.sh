#!/usr/bin/env bash
# Generate EVIDENCE.md's claim tables from the property registry
# (PrivateGames/Evidence.lean). Each section's table sits between
#   <!-- BEGIN GENERATED: <Section> -->  and  <!-- END GENERATED: <Section> -->
# and is replaced by the registry's table. Prose outside the markers is
# hand-written and left alone.
#
#   ./scripts/gen_evidence.sh          rewrite EVIDENCE.md
#   ./scripts/gen_evidence.sh --check  fail if EVIDENCE.md is out of date (CI)
set -euo pipefail
cd "$(dirname "$0")/.."
tmp=$(mktemp -t evidence).lean
printf 'import PrivateGames.Evidence\n#evidence_tables\n' > "$tmp"
raw=$(lake env lean "$tmp" 2>&1) || { echo "$raw"; exit 1; }
gen=$(mktemp -t evidence_gen)
# Strip the "<file>:<line>:<col>: info: " prefix from the first line.
echo "$raw" | sed -E '1s/^[^ ]*: info: //' > "$gen"
out=$(mktemp -t evidence_out)
python3 - "$gen" EVIDENCE.md "$out" <<'PY'
import re, sys
gen, src, dst = sys.argv[1:4]
blocks = dict(re.findall(r"<!-- BEGIN GENERATED: (.+?) -->\n(.*?)\n<!-- END GENERATED: \1 -->", open(gen).read(), re.S))
text = open(src).read()
seen = set()
def repl(m):
    name = m.group(1)
    if name not in blocks:
        sys.exit(f"EVIDENCE.md has a generated section '{name}' with no registered claims")
    seen.add(name)
    return f"<!-- BEGIN GENERATED: {name} -->\n{blocks[name]}\n<!-- END GENERATED: {name} -->"
text = re.sub(r"<!-- BEGIN GENERATED: (.+?) -->\n(?:.*?\n)?<!-- END GENERATED: \1 -->", repl, text, flags=re.S)
missing = set(blocks) - seen
if missing:
    sys.exit(f"registered sections missing from EVIDENCE.md: {sorted(missing)}")
open(dst, "w").write(text)
PY
if [ "${1:-}" = "--check" ]; then
  if ! diff -u EVIDENCE.md "$out"; then
    echo "EVIDENCE.md is out of date: run ./scripts/gen_evidence.sh"; exit 1
  fi
  echo "EVIDENCE.md claim tables match the registry"
else
  cp "$out" EVIDENCE.md
  echo "EVIDENCE.md claim tables regenerated"
fi
