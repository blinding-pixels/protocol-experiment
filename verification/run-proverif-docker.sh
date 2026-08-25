#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
OUT="/tmp/assumption-recheck/proverif-run"
SNAPSHOT="$OUT/snapshot"
MODELS="$OUT/models"
mkdir -p "$SNAPSHOT" "$MODELS"

bash "$ROOT/archives/text-snapshot/RESTORE.sh" "$OUT/source.tar.xz"
tar -xJf "$OUT/source.tar.xz" -C "$SNAPSHOT"

for model in \
  composition_symbolic.pv \
  secret_state_union_resurrection.pv \
  role_authorization_symbolic.pv \
  role_authorization_bypass.pv \
  role_context_binding_bypass.pv; do
  source_path="$(find "$SNAPSHOT" -type f -name "$model" | sort | head -n 1)"
  test -n "$source_path"
  cp "$source_path" "$MODELS/$model"
done
cp "$ROOT/verification/authorization_lifecycle_revalidation.pv" "$MODELS/"
sha256sum "$MODELS"/*.pv > "$OUT/proverif-inputs.sha256"

cat > "$OUT/ProVerif.Dockerfile" <<'DOCKER'
FROM ocaml/opam:debian-12-ocaml-4.14
USER root
RUN apt-get update \
 && apt-get install -y --no-install-recommends libgtk2.0-dev pkg-config \
 && rm -rf /var/lib/apt/lists/*
USER opam
RUN opam update && opam install --yes proverif.2.05
WORKDIR /work
ENTRYPOINT ["opam", "exec", "--", "proverif"]
DOCKER

docker build --pull --progress=plain \
  --tag protocol-assumption-proverif:2.05 \
  --file "$OUT/ProVerif.Dockerfile" \
  "$OUT" 2>&1 | tee "$OUT/proverif-docker-build.txt"

docker image inspect protocol-assumption-proverif:2.05 \
  --format '{{json .Id}} {{json .RepoDigests}}' \
  | tee "$OUT/proverif-image.txt"

docker run --rm --entrypoint sh \
  protocol-assumption-proverif:2.05 \
  -lc 'opam list --installed --columns=name,version proverif' \
  | tee "$OUT/proverif-version.txt"

run_model() {
  local model="$1"
  local output="$2"
  docker run --rm \
    --volume "$MODELS:/work:ro" \
    --workdir /work \
    protocol-assumption-proverif:2.05 "$model" \
    2>&1 | tee "$output"
}

run_model composition_symbolic.pv "$OUT/proverif-composition.txt"
test "$(grep -c 'RESULT not attacker.* is true' "$OUT/proverif-composition.txt")" -eq 3
! grep -Eq 'RESULT not attacker.* (is false|cannot be proved)' "$OUT/proverif-composition.txt"

run_model secret_state_union_resurrection.pv "$OUT/proverif-secret-union.txt"
test "$(grep -c 'RESULT not attacker.* is false' "$OUT/proverif-secret-union.txt")" -eq 2

run_model role_authorization_symbolic.pv "$OUT/proverif-role-authorization.txt"
test "$(grep -c 'RESULT event(OperationAccepted.* is true' "$OUT/proverif-role-authorization.txt")" -eq 3
grep -Fq 'RESULT not attacker(responseCanary[]) is false.' \
  "$OUT/proverif-role-authorization.txt"
grep -Fq 'RESULT not attacker(postRevokeAcceptanceCanary[]) is true.' \
  "$OUT/proverif-role-authorization.txt"

run_model role_authorization_bypass.pv "$OUT/proverif-role-bypass.txt"
grep -q 'RESULT event(OperationAccepted.* is false' "$OUT/proverif-role-bypass.txt"

run_model role_context_binding_bypass.pv "$OUT/proverif-context-bypass.txt"
grep -q 'RESULT event(OperationAccepted.* is false' "$OUT/proverif-context-bypass.txt"

run_model authorization_lifecycle_revalidation.pv "$OUT/proverif-lifecycle.txt"
grep -Fq 'RESULT not attacker(removalOnlyRevivalCanary[]) is false.' \
  "$OUT/proverif-lifecycle.txt"
grep -Fq 'RESULT not attacker(coupledOldCredentialCanary[]) is true.' \
  "$OUT/proverif-lifecycle.txt"
grep -Fq 'RESULT not attacker(coupledHonestCanary[]) is false.' \
  "$OUT/proverif-lifecycle.txt"
grep -Fq 'RESULT not attacker(freshIncarnationOldCredentialCanary[]) is true.' \
  "$OUT/proverif-lifecycle.txt"
grep -Fq 'RESULT not attacker(freshIncarnationHonestCanary[]) is false.' \
  "$OUT/proverif-lifecycle.txt"
test "$(grep -c 'RESULT event(.* is true' "$OUT/proverif-lifecycle.txt")" -eq 2

cat > "$OUT/result.json" <<JSON
{
  "result": "pass",
  "source_commit": "${GITHUB_SHA:-local}",
  "proverif_version": "2.05",
  "container_image": "protocol-assumption-proverif:2.05",
  "historical_models_rechecked": 5,
  "new_lifecycle_model_rechecked": true,
  "membership_only_same_identity_revival_reachable": true,
  "coupled_role_tombstone_blocks_old_credential": true,
  "fresh_incarnation_blocks_old_credential": true,
  "honest_corrected_paths_reachable": true
}
JSON
