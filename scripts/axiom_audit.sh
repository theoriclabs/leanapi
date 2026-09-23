#!/usr/bin/env bash
# Proof audit: `#print axioms` for every theorem listed in
# scripts/audited_theorems.txt. Fails if any depends on `sorryAx`, or on an
# axiom outside the standard three (propext, Classical.choice, Quot.sound).
# `Lean.ofReduceBool` (native_decide) also fails the audit.
set -euo pipefail
cd "$(dirname "$0")/.."
list=scripts/audited_theorems.txt
mods=$(grep -v '^#' "$list" | awk 'NF==2 {print $1}' | sort -u || true)
names=$(grep -v '^#' "$list" | awk 'NF==2 {print $2}' || true)
if [ -z "$names" ]; then echo "axiom audit: no theorems listed"; exit 0; fi
# Build every audited module (some, like Notes.Shared, are not reached by
# the default targets).
lake build $mods >/dev/null
tmp=$(mktemp -t audit).lean
{
  for m in $mods; do echo "import $m"; done
  for n in $names; do echo "#print axioms $n"; done
} > "$tmp"
out=$(lake env lean "$tmp" 2>&1) || { echo "$out"; exit 1; }
echo "$out"
if echo "$out" | grep -E "sorryAx|ofReduceBool|ofReduceNat" >/dev/null; then
  echo "axiom audit FAILED"; exit 1
fi
bad=$(echo "$out" | grep -oE "depends on axioms: \[[^]]*\]" | tr -d '[]' | sed 's/depends on axioms: //' | tr ',' '\n' | tr -d ' ' | grep -vE '^(propext|Classical.choice|Quot.sound)$' | sort -u || true)
if [ -n "$bad" ]; then echo "unexpected axioms: $bad"; echo "axiom audit FAILED"; exit 1; fi
count=$(echo "$names" | wc -w | tr -d ' ')
echo "axiom audit passed ($count theorems)"
