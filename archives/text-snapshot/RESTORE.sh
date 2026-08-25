#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
out="${1:-$here/causal-dag-assurance-text-000b7a1.tar.xz}"
cat "$here"/part-* | base64 --decode > "$out"
printf '%s  %s\n' db309e499865a3d6fec690d47e39626bb71ff5902a064e4c8b968f69a0c5787b "$out" | sha256sum -c -
echo "Verified $out"
echo "Extract with: tar -xJf '$out'"
