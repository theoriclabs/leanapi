#!/usr/bin/env bash
# Every LeanAPI gate of the domain stack (milestone 3), on this repository's own Lake build:
# LeanApi.Core (portable), LeanApi.Native, the fixture apps over HTTP and SQLite, the post's
# api (`partiful_v2/Domain.lean`, staged by scripts/stage_partiful_api.py), and the proofs that
# LeanAPI imports no LeanReact, LeanJS or LeanApp and that its library code stays general.
# Usage: scripts/ddd_check.sh [SUMMARY_FILE]   (from the repository root)
set -u
cd "$(dirname "$0")/.."
summary=${1:-.lake/ddd-check.summary}
logs=$(dirname "$summary")
mkdir -p "$logs"
: > "$summary"
export LEAN_NUM_THREADS=${LEAN_NUM_THREADS:-2}
step() { echo "== $1: exit $2" >> "$summary"; }
run() { local name=$1; shift; "$@" > "$logs/ddd-check-$name.log" 2>&1; step "$name" $?; }
date >> "$summary"
free=$(df -k . | tail -1 | awk '{print $4}')
echo "-- free: $((free / 1024)) MB" >> "$summary"
if [ "$free" -lt 512000 ]; then echo "STOPPED: under 500 MB free" >> "$summary"; exit 1; fi

run stage python3 scripts/stage_partiful_api.py
run build lake build LeanApi LeanContract LeanApiCore TestsCore TestsNative \
  leanapi_tests leanapi_core_tests leanapi_native_checks leanapi_apps leanapi_counter_app leanapi_partiful_api
run leanapi_tests .lake/build/bin/leanapi_tests
run core_tests .lake/build/bin/leanapi_core_tests
run rejections python3 scripts/check_core_fixtures.py
for check in contract prepared kdf read command routes post; do
  run "native_$check" .lake/build/bin/leanapi_native_checks "$check"
done
run counter_acceptance node scripts/ddd_counter_acceptance.mjs
run library_acceptance node scripts/ddd_library_acceptance.mjs --save docs/ddd-m2-library-transcript.txt
run migration_acceptance node scripts/ddd_migration_acceptance.mjs
run curl_acceptance node scripts/ddd_route_acceptance.mjs
run partiful_api_acceptance node scripts/ddd_partiful_api_acceptance.mjs
run post_transcript node scripts/ddd_post_transcript.mjs --save docs/ddd-m2-post-transcript.txt
run partiful_transcript node scripts/ddd_post_transcript.mjs --exe leanapi_partiful_api --save docs/ddd-m2-partiful-transcript.txt
run client_post node scripts/ddd_client_acceptance.mjs post
run client_library node scripts/ddd_client_acceptance.mjs library
run diff_check git diff --check
imports=$(grep -rnE '^import (LeanReact|LeanJS|LeanApp)' --include='*.lean' . | grep -v '/\.lake/' | wc -l | tr -d ' ')
requires=$(grep -A1 '^\[\[require\]\]' lakefile.toml | grep -ciE 'name = "(leanreact|leanjs)"')
requires=$((requires + $(grep -ciE '"name": "(leanreact|leanjs)"' lake-manifest.json)))
echo "-- imports of LeanReact/LeanJS/LeanApp: $imports; leanreact requires: $requires" >> "$summary"
general=$(grep -rniEw 'partiful|party|parties|rsvps?|persons?|people|guests?|attendees?|guestlist|the post' \
  LeanApi/Core LeanApi/Core.lean LeanApi/Native LeanApi/Native.lean LeanApi/Publication LeanApi/Publication.lean \
  LeanContract LeanContract.lean | wc -l | tr -d ' ')
echo "-- generality hits in library code: $general" >> "$summary"
for log in core_tests leanapi_tests native_routes native_post counter_acceptance library_acceptance \
    migration_acceptance curl_acceptance partiful_api_acceptance rejections; do
  echo "   $log: $(grep -aE 'PASS|passed' "$logs/ddd-check-$log.log" | tail -1)" >> "$summary"
done
df -h . | tail -1 >> "$summary"
date >> "$summary"
echo DONE >> "$summary"
