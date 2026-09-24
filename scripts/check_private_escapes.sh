#!/usr/bin/env bash
# Capabilities are not forged outside the framework.
#
# `Auth α` (an authenticated actor) has a private constructor, so application
# code cannot write `⟨otherUser⟩ : Auth UserId`. Lean 4 has no friend modules,
# so the framework's other files reach it through the `LeanApi.Internal`
# namespace (`Internal.authOf`). This check refuses any mention of that
# namespace outside `LeanApi/` and `tests/`: examples and applications get
# actors only from authentication.
#
#   ./scripts/check_private_escapes.sh    exit 1 on any use outside the framework
set -euo pipefail
cd "$(dirname "$0")/.."
hits=$(grep -rn --include='*.lean' -E '\bInternal\.authOf\b|\bLeanApi\.Internal\b|^\s*open\s+.*\bInternal\b' . \
  | grep -v -E '^\./(\.lake|LeanApi|tests)/' || true)
if [ -n "$hits" ]; then
  echo "LeanApi.Internal used outside the framework (only authentication may make an Auth):"
  echo "$hits"
  exit 1
fi
echo "no framework internals used outside LeanApi/ and tests/"
