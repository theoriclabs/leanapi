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
if [ "$fail" -ne 0 ]; then echo "README snippet check FAILED"; exit 1; fi
echo "README snippet check passed ($count snippets)"
