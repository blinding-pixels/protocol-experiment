"""Conjunctive identity checks for dual-target attack results.

The old prototype accepted the first digest field that happened to match. This
module treats result identity, source provenance, and every supplied attack
digest as independent requirements and returns structured diagnostics.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from typing import Any, Mapping, Sequence

DIGEST_FIELDS: tuple[str, ...] = ("attack_input_digest", "transcript_digest")
RESULT_IDENTITY_FIELDS: tuple[str, ...] = (
    "schema",
    "scenario",
    "layer",
    "source_commit",
)
PROVENANCE_IDENTITY_FIELDS: tuple[str, ...] = (
    "variant",
    "sha256",
    "size",
    "source_commit",
    "source_tree_sha256",
    "broken_feature_count",
)


@dataclass(frozen=True)
class AttackIdentityComparison:
    """Machine-readable result of one dual-target identity comparison."""

    valid: bool
    compared_digest_fields: tuple[str, ...]
    matched_result_fields: tuple[str, ...]
    source_commit: str | None
    source_tree_sha256: str | None
    left_binary_sha256: str | None
    right_binary_sha256: str | None
    errors: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _is_lower_hex(value: object, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _require_equal_nonempty_string(
    left: Mapping[str, Any],
    right: Mapping[str, Any],
    field: str,
    errors: list[str],
    matched: list[str],
) -> str | None:
    left_value = left.get(field)
    right_value = right.get(field)
    if not isinstance(left_value, str) or not left_value:
        errors.append(f"left result has no non-empty {field}")
        return None
    if not isinstance(right_value, str) or not right_value:
        errors.append(f"right result has no non-empty {field}")
        return None
    if left_value != right_value:
        errors.append(f"{field} mismatch: {left_value!r} != {right_value!r}")
        return None
    matched.append(field)
    return left_value


def _validated_execution_identity(
    result: Mapping[str, Any], label: str, errors: list[str]
) -> Mapping[str, Any] | None:
    provenance = result.get("execution_provenance")
    if not isinstance(provenance, Mapping):
        errors.append(f"{label} result has no execution_provenance object")
        return None
    if provenance.get("same_binary_identity_through_execution") is not True:
        errors.append(f"{label} binary identity was not stable through execution")

    before = provenance.get("verified_before")
    after = provenance.get("verified_after")
    if not isinstance(before, Mapping) or not isinstance(after, Mapping):
        errors.append(f"{label} execution provenance lacks before/after identities")
        return None

    for field in PROVENANCE_IDENTITY_FIELDS:
        if field not in before:
            errors.append(f"{label} verified_before lacks {field}")
        if field not in after:
            errors.append(f"{label} verified_after lacks {field}")
        if field in before and field in after and before[field] != after[field]:
            errors.append(f"{label} {field} changed during execution")

    top_commit = result.get("source_commit")
    if before.get("source_commit") != top_commit or after.get("source_commit") != top_commit:
        errors.append(f"{label} embedded source_commit disagrees with verified binary")
    top_variant = result.get("variant")
    if before.get("variant") != top_variant or after.get("variant") != top_variant:
        errors.append(f"{label} runtime variant disagrees with verified binary")

    if not _is_lower_hex(before.get("source_commit"), 40):
        errors.append(f"{label} provenance has invalid source_commit format")
    if not _is_lower_hex(before.get("source_tree_sha256"), 64):
        errors.append(f"{label} provenance has invalid source_tree_sha256 format")
    if not _is_lower_hex(before.get("sha256"), 64):
        errors.append(f"{label} provenance has invalid binary SHA-256 format")
    return before


def compare_attack_identity(
    left: Mapping[str, Any],
    right: Mapping[str, Any],
    *,
    expected_scenario: str | None = None,
    expected_layer: str | None = None,
    expected_left_variant: str | None = None,
    expected_right_variant: str | None = None,
    additional_equal_fields: Sequence[str] = (),
    require_distinct_binaries: bool = True,
) -> AttackIdentityComparison:
    """Require every independent identity condition to hold conjunctively."""

    errors: list[str] = []
    matched: list[str] = []

    values: dict[str, str | None] = {}
    for field in RESULT_IDENTITY_FIELDS:
        values[field] = _require_equal_nonempty_string(
            left, right, field, errors, matched
        )

    if expected_scenario is not None:
        if values.get("scenario") != expected_scenario:
            errors.append(
                f"scenario is not the requested fixture: {values.get('scenario')!r} != {expected_scenario!r}"
            )
    if expected_layer is not None:
        if values.get("layer") != expected_layer:
            errors.append(
                f"layer is not the requested layer: {values.get('layer')!r} != {expected_layer!r}"
            )
    if expected_left_variant is not None and left.get("variant") != expected_left_variant:
        errors.append(
            f"left variant mismatch: {left.get('variant')!r} != {expected_left_variant!r}"
        )
    if expected_right_variant is not None and right.get("variant") != expected_right_variant:
        errors.append(
            f"right variant mismatch: {right.get('variant')!r} != {expected_right_variant!r}"
        )

    for field in additional_equal_fields:
        if field not in left or field not in right:
            errors.append(f"{field} must be present on both results")
        elif left[field] != right[field]:
            errors.append(f"{field} mismatch: {left[field]!r} != {right[field]!r}")
        else:
            matched.append(field)

    compared_digests: list[str] = []
    for field in DIGEST_FIELDS:
        supplied = field in left or field in right
        if not supplied:
            continue
        if field not in left or field not in right:
            errors.append(f"{field} is present on only one result")
            continue
        left_digest = left[field]
        right_digest = right[field]
        if not _is_lower_hex(left_digest, 64):
            errors.append(f"left {field} is not a 64-character lowercase hex digest")
            continue
        if not _is_lower_hex(right_digest, 64):
            errors.append(f"right {field} is not a 64-character lowercase hex digest")
            continue
        compared_digests.append(field)
        if left_digest != right_digest:
            errors.append(f"{field} mismatch")

    if not compared_digests:
        errors.append("no attack-input or transcript digest was compared")

    left_provenance = _validated_execution_identity(left, "left", errors)
    right_provenance = _validated_execution_identity(right, "right", errors)
    source_tree: str | None = None
    left_binary: str | None = None
    right_binary: str | None = None
    if left_provenance is not None and right_provenance is not None:
        left_tree = left_provenance.get("source_tree_sha256")
        right_tree = right_provenance.get("source_tree_sha256")
        if left_tree != right_tree:
            errors.append("verified source_tree_sha256 mismatch")
        elif isinstance(left_tree, str):
            source_tree = left_tree

        left_binary_value = left_provenance.get("sha256")
        right_binary_value = right_provenance.get("sha256")
        if isinstance(left_binary_value, str):
            left_binary = left_binary_value
        if isinstance(right_binary_value, str):
            right_binary = right_binary_value
        if require_distinct_binaries and left_binary_value == right_binary_value:
            errors.append("dual-target comparison resolved to identical binary bytes")

        verified_commit = left_provenance.get("source_commit")
        if verified_commit != right_provenance.get("source_commit"):
            errors.append("verified binary source_commit mismatch")
        if values.get("source_commit") != verified_commit:
            errors.append("result source_commit is not the verified binary source_commit")

    return AttackIdentityComparison(
        valid=not errors,
        compared_digest_fields=tuple(compared_digests),
        matched_result_fields=tuple(matched),
        source_commit=values.get("source_commit"),
        source_tree_sha256=source_tree,
        left_binary_sha256=left_binary,
        right_binary_sha256=right_binary,
        errors=tuple(errors),
    )
