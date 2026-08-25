"""Validation for evidence that is valid only for one exact binary and target."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


@dataclass(frozen=True)
class TargetEvidenceValidation:
    valid: bool
    errors: tuple[str, ...]


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _hex(value: object, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def validate_target_identity(target: object) -> list[str]:
    errors: list[str] = []
    if not isinstance(target, Mapping):
        return ["target must be an object"]
    for field in (
        "target_triple",
        "operating_system",
        "os_release",
        "architecture",
        "cpu_model",
        "compiler",
        "optimization_profile",
    ):
        value = target.get(field)
        if not isinstance(value, str) or not value:
            errors.append(f"target.{field} must be a non-empty string")
    return errors


def validate_target_bound_measurement(
    record: Mapping[str, Any],
    binary_manifest: Mapping[str, Any],
    *,
    root: Path,
) -> TargetEvidenceValidation:
    errors: list[str] = []
    if record.get("schema") != "causal-dag-assurance.target-measurement.v1":
        errors.append("unexpected measurement schema")

    for field, length in (
        ("binary_sha256", 64),
        ("source_commit", 40),
        ("source_tree_sha256", 64),
        ("artifact_sha256", 64),
    ):
        if not _hex(record.get(field), length):
            errors.append(f"invalid {field}")

    for field in ("binary_sha256", "source_commit", "source_tree_sha256"):
        if record.get(field) != binary_manifest.get(field):
            errors.append(f"measurement {field} does not match the binary manifest")

    errors.extend(validate_target_identity(record.get("target")))
    if record.get("target") != binary_manifest.get("target"):
        errors.append("measurement target does not exactly match the binary target")

    relative = record.get("artifact_path")
    if not isinstance(relative, str) or not relative:
        errors.append("artifact_path must be a non-empty relative path")
    else:
        candidate = (root / relative).resolve()
        try:
            candidate.relative_to(root.resolve())
        except ValueError:
            errors.append("artifact_path escapes the evidence root")
        else:
            if not candidate.is_file():
                errors.append(f"missing measurement artifact: {relative}")
            elif sha256_file(candidate) != record.get("artifact_sha256"):
                errors.append("measurement artifact SHA-256 mismatch")

    return TargetEvidenceValidation(valid=not errors, errors=tuple(errors))


def supports_exact_target(
    record: Mapping[str, Any], requested_target: Mapping[str, Any]
) -> bool:
    """Never infer support for a target that was not the measured target."""

    return record.get("target") == dict(requested_target)
