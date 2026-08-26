#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="/tmp/assumption-recheck/lean"
SNAPSHOT="$OUT/snapshot"
WORK="$OUT/work"
mkdir -p "$SNAPSHOT" "$WORK"

bash "$ROOT/archives/text-snapshot/RESTORE.sh" "$OUT/source.tar.xz"
tar -xJf "$OUT/source.tar.xz" -C "$SNAPSHOT"

logic="$(find "$SNAPSHOT" -type f -path '*/CausalDagCgka/Logic.lean' | sort | head -n 1)"
authorization="$(find "$SNAPSHOT" -type f -path '*/CausalDagCgka/Authorization.lean' | sort | head -n 1)"
lifecycle="$ROOT/formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean"

test -n "$logic"
test -n "$authorization"
test -f "$lifecycle"
printf '%s  %s\n' \
  4752e466de814da45bea15df8aaefe35af1853ea0f1e700fab151f76f90a9730 \
  "$lifecycle" | sha256sum -c -

{
  cat "$logic"
  sed '/^import CausalDagCgka\.Logic$/d' "$authorization"
  sed '/^import CausalDagCgka\.Authorization$/d' "$lifecycle"
  cat <<'LEAN'

#print axioms CausalDagCgka.AuthorizationLifecycle.removal_only_blocks_while_membership_inactive
#print axioms CausalDagCgka.AuthorizationLifecycle.removal_only_same_identity_rejoin_revives_capability
#print axioms CausalDagCgka.AuthorizationLifecycle.coupled_removal_prevents_same_identity_capability_revival
#print axioms CausalDagCgka.AuthorizationLifecycle.fresh_incarnation_does_not_inherit_old_capability
LEAN
} > "$WORK/AuthorizationLifecycleSelfContained.lean"

if grep -nE '\b(sorry|admit)\b|sorryAx' \
    "$WORK/AuthorizationLifecycleSelfContained.lean"; then
  echo 'proof placeholder found'
  exit 1
fi

sha256sum \
  "$OUT/source.tar.xz" \
  "$WORK/AuthorizationLifecycleSelfContained.lean" \
  > "$OUT/lean-inputs.sha256"

curl --fail --location --retry 5 --retry-all-errors \
  https://github.com/cauli/lean4-wasm-in-browser/releases/download/test-fixtures-4.33/lean-wasm-4.33-testfixture.tar.gz \
  --output "$OUT/lean-wasm.tar.gz"
printf '%s  %s\n' \
  fb6e0cb754053deb247eea8b2506a89ac7c1e887a976d61b45cbe8012b3a5f34 \
  "$OUT/lean-wasm.tar.gz" | sha256sum -c -
mkdir -p "$OUT/lean-wasm"
tar -xzf "$OUT/lean-wasm.tar.gz" -C "$OUT/lean-wasm"

curl --fail --location --retry 5 --retry-all-errors \
  https://raw.githubusercontent.com/cauli/lean4-wasm-in-browser/2655455848091557c8457b6a3b03c291859890e6/scripts/lean-wasm-node.cjs \
  --output "$OUT/lean-wasm-node.cjs"

lean_js="$(find "$OUT/lean-wasm" -type f -path '*/bin/lean.js' | head -n 1)"
test -n "$lean_js"
artifact="$(dirname "$(dirname "$lean_js")")"
test -f "$artifact/bin/lean.js"
test -f "$artifact/bin/lean.wasm"
test -d "$artifact/lib/lean"
printf '%s\n' "$artifact" > "$OUT/lean-wasm-artifact-root.txt"

export LEAN_WASM_NODE_MEMORY_MB=1024
node --stack-size=8192 \
  "$OUT/lean-wasm-node.cjs" \
  "$artifact" "$WORK" --version \
  2>&1 | tee "$OUT/lean-wasm-version.txt"

node --stack-size=8192 \
  "$OUT/lean-wasm-node.cjs" \
  "$artifact" "$WORK" \
  /work/AuthorizationLifecycleSelfContained.lean \
  2>&1 | tee "$OUT/lean-wasm-result.txt"

! grep -Eiq '(^|[^[:alpha:]])error:' "$OUT/lean-wasm-result.txt"
test "$(grep -c 'depends on axioms' "$OUT/lean-wasm-result.txt" || true)" -eq 4
! grep -Fq 'sorryAx' "$OUT/lean-wasm-result.txt"

cat > "$OUT/result.json" <<JSON
{
  "result": "pass",
  "source_commit": "${GITHUB_SHA:-local}",
  "current_lifecycle_sha256": "4752e466de814da45bea15df8aaefe35af1853ea0f1e700fab151f76f90a9730",
  "wasm_fixture_sha256": "fb6e0cb754053deb247eea8b2506a89ac7c1e887a976d61b45cbe8012b3a5f34",
  "wasm_fixture_release": "test-fixtures-4.33",
  "exact_project_pin_checked": false,
  "project_pin": "leanprover/lean4:v4.32.2",
  "note": "This is a real Lean WASM elaborator/kernel check under the 4.33-pre fixture; it is intentionally not promoted to exact 4.32.2 evidence."
}
JSON
