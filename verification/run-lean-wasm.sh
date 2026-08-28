#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
SOURCE="$ROOT/formal/current-source/CausalDagCgka"
OUT="${LEAN_WASM_OUT:-/tmp/protocol-lean-full-wasm}"
WORK="$OUT/work"
FIXTURE="$OUT/lean-wasm-4.33-testfixture.tar.gz"
FIXTURE_SHA256="fb6e0cb754053deb247eea8b2506a89ac7c1e887a976d61b45cbe8012b3a5f34"
DRIVER="$OUT/lean-wasm-node.cjs"
DRIVER_SHA256="54851bfe112a00f5ae0355afb58cf6d8c92b2e92cc2ce5168cd8e37af6a4ba24"
FULL_SOURCE="$WORK/FullCombinatorialSpine.lean"
AUDIT_SOURCE="$WORK/FullCombinatorialSpineAudit.lean"
RESULT="$OUT/lean-wasm-full-result.txt"

modules=(
  Logic Authorization Accountability CausalIdeal KappaExposure Exposure
  Puncture PublicState RegionCover SegmentGrant Separation
  AuthorizationLifecycle Main
)

mkdir -p "$OUT" "$WORK"
for module in "${modules[@]}"; do
  test -f "$SOURCE/$module.lean"
done

# This fixture writes exported-only .olean snapshots, which omit private helper
# declarations used by this historical package. Check the exact complete source
# closure in one kernel invocation instead of mistaking that fixture limitation
# for a proof failure.
sed -n '1p' "$SOURCE/Logic.lean" > "$FULL_SOURCE"
for module in \
  Logic Authorization Accountability CausalIdeal KappaExposure Exposure \
  Puncture PublicState RegionCover SegmentGrant Separation \
  AuthorizationLifecycle Main; do
  sed '/^import /d' "$SOURCE/$module.lean" >> "$FULL_SOURCE"
done

if grep -nE '\b(sorry|admit)\b|sorryAx|^[[:space:]]*(axiom|unsafe)[[:space:]]' \
    "$FULL_SOURCE"; then
  echo 'proof placeholder or declared escape hatch found' >&2
  exit 1
fi

cp "$FULL_SOURCE" "$AUDIT_SOURCE"
for module in "${modules[@]}"; do
  awk '
    /^namespace[[:space:]]+/ { ns[++depth]=$2; next }
    /^end([[:space:]]+|$)/ { if (depth > 0) depth--; next }
    /^theorem[[:space:]]+/ {
      name=$2
      sub(/[^A-Za-z0-9_].*/, "", name)
      full=""
      for (i=1; i<=depth; i++) full=full (i>1 ? "." : "") ns[i]
      print "#print axioms " full "." name
    }
  ' "$SOURCE/$module.lean" >> "$AUDIT_SOURCE"
done

audit_count="$(grep -c '^#print axioms ' "$AUDIT_SOURCE")"
test "$audit_count" -gt 0
sha256sum "$SOURCE"/*.lean "$FULL_SOURCE" "$AUDIT_SOURCE" > "$OUT/lean-inputs.sha256"

if ! printf '%s  %s\n' "$FIXTURE_SHA256" "$FIXTURE" | \
    sha256sum -c - >/dev/null 2>&1; then
  curl --fail --location --retry 5 --retry-all-errors \
    https://github.com/cauli/lean4-wasm-in-browser/releases/download/test-fixtures-4.33/lean-wasm-4.33-testfixture.tar.gz \
    --output "$FIXTURE"
fi
printf '%s  %s\n' "$FIXTURE_SHA256" "$FIXTURE" | sha256sum -c -

mkdir -p "$OUT/lean-wasm"
tar -xzf "$FIXTURE" -C "$OUT/lean-wasm"
curl --fail --location --retry 5 --retry-all-errors \
  https://raw.githubusercontent.com/cauli/lean4-wasm-in-browser/2655455848091557c8457b6a3b03c291859890e6/scripts/lean-wasm-node.cjs \
  --output "$DRIVER"
printf '%s  %s\n' "$DRIVER_SHA256" "$DRIVER" | sha256sum -c -

lean_js="$(rg --files "$OUT/lean-wasm" | rg '/bin/lean\.js$' | head -n 1)"
test -n "$lean_js"
artifact="$(dirname "$(dirname "$lean_js")")"
test -f "$artifact/bin/lean.wasm"
test -d "$artifact/lib/lean"

node_bin=(node)
node_major="$(node -p 'process.versions.node.split(".")[0]')"
if test "$node_major" -lt 26 && test -x /opt/homebrew/bin/node; then
  homebrew_node_major="$(/opt/homebrew/bin/node -p \
    'process.versions.node.split(".")[0]')"
  if test "$homebrew_node_major" -ge 26; then
    node_bin=(/opt/homebrew/bin/node)
    node_major="$homebrew_node_major"
  fi
fi
if test "$node_major" -lt 26; then
  # Node 24 rejects this fixture because its 104,709 exports exceed V8's old
  # 100,000-export ceiling. Pin the known-good runtime instead.
  node_bin=(npx --yes node@26.0.0)
fi

export LEAN_WASM_NODE_MEMORY_MB=2048
set +e
"${node_bin[@]}" --stack-size=8192 \
  "$DRIVER" "$artifact" "$WORK" --version \
  2>&1 | tee "$OUT/lean-wasm-version.txt"
set -e
grep -Fq 'Lean (version 4.33.0-pre' "$OUT/lean-wasm-version.txt"

set +e
"${node_bin[@]}" --stack-size=8192 \
  "$DRIVER" "$artifact" "$WORK" /work/FullCombinatorialSpineAudit.lean \
  2>&1 | tee "$RESULT"
set -e

! grep -Eiq '(^|[^[:alpha:]])error:' "$RESULT"
grep -Fq 'hasErrors = false' "$RESULT"
test "$(grep -Ec 'depends on axioms|does not depend on any axioms' "$RESULT")" \
  -eq "$audit_count"
! grep -Fq 'sorryAx' "$RESULT"

actual_axioms="$(perl -0777 -ne '
  while (/depends on axioms:\s*\[([^\]]*)\]/g) {
    $x=$1; $x=~s/\s+//g;
    for $a (split /,/, $x) { $seen{$a}=1 if length $a }
  }
  END { print "$_\n" for sort keys %seen }
' "$RESULT")"
test "$actual_axioms" = $'Quot.sound\npropext'

depends_count="$(grep -c 'depends on axioms' "$RESULT")"
axiom_free_count="$(grep -c 'does not depend on any axioms' "$RESULT")"
source_sha256="$(sha256sum "$FULL_SOURCE" | cut -d ' ' -f 1)"

cat > "$OUT/result.json" <<JSON
{
  "result": "pass",
  "source_commit": "${GITHUB_SHA:-local}",
  "full_source_sha256": "$source_sha256",
  "theorem_count": $audit_count,
  "theorems_using_standard_axioms": $depends_count,
  "axiom_free_theorems": $axiom_free_count,
  "allowed_axioms": ["propext", "Quot.sound"],
  "wasm_fixture_sha256": "$FIXTURE_SHA256",
  "wasm_fixture_release": "test-fixtures-4.33",
  "exact_project_pin_checked": false,
  "project_pin": "leanprover/lean4:v4.32.2",
  "note": "Real Lean WASM elaborator/kernel check under 4.33.0-pre; exact 4.32.2 lake build remains required."
}
JSON
