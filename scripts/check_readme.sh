#!/usr/bin/env bash
# README snippet check: every ```lean block in README.md must compile.
# Each block is compiled on its own, so blocks may reuse names.
# Blocks that start with `-- sketch` are skipped (illustrative only).
set -euo pipefail
cd "$(dirname "$0")/.."
dir=$(mktemp -d -t readme)
awk -v dir="$dir" '
  /^```lean[[:space:]]*$/ { n++; f = sprintf("%s/snippet%02d.lean", dir, n); inb = 1; next }
  /^```/ && inb { inb = 0; close(f); next }
  inb { print > f }
' README.md
fail=0; count=0
for f in "$dir"/snippet*.lean; do
  [ -e "$f" ] || continue
  if head -1 "$f" | grep -q '^-- sketch'; then continue; fi
  count=$((count + 1))
  if ! out=$(lake env lean "$f" 2>&1); then
    echo "README snippet $(basename "$f") failed:"; echo "$out"; fail=1
  elif echo "$out" | grep -q "error"; then
    echo "README snippet $(basename "$f") reported errors:"; echo "$out"; fail=1
  fi
done
# A block preceded by `<!-- file: PATH -->` must be exactly that file, so the
# README and the runnable examples cannot drift apart.
if ! python3 - <<'PY'
import re, sys
text = open("README.md").read()
bad = 0
for m in re.finditer(r"<!-- file: (\S+) -->\s*\n```lean\n(.*?)\n```", text, re.S):
    path, block = m.group(1), m.group(2)
    try:
        body = open(path).read().rstrip("\n")
    except FileNotFoundError:
        print(f"README names {path}, which does not exist"); bad = 1; continue
    if block.rstrip("\n") != body:
        print(f"README block for {path} differs from the file"); bad = 1
sys.exit(bad)
PY
then fail=1; fi
if [ "$fail" -ne 0 ]; then echo "README snippet check FAILED"; exit 1; fi
echo "README snippet check passed ($count snippets, examples match their files)"
