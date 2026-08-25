"""Reject historical green artifacts as substitutes for exact frozen-source evidence."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping


@dataclass(frozen=True)
class HistoricalArtifactValidation:
    valid: bool
    errors: tuple[str, ...]


def _hex(value: object, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_historical_artifact_boundary(
    document: Mapping[str, Any], *, root: Path
) -> HistoricalArtifactValidation:
    errors: list[str] = []
    if document.get("schema") != "causal-dag-assurance.historical-artifact-boundary.v1":
        errors.append("unexpected historical-artifact schema")

    frozen_commit = document.get("frozen_source_commit")
    frozen_tree = document.get("frozen_source_tree")
    if not _hex(frozen_commit, 40):
        errors.append("invalid frozen_source_commit")
    if not _hex(frozen_tree, 40):
        errors.append("invalid frozen_source_tree")

    required_layer = document.get("required_layer")
    if not isinstance(required_layer, str) or not required_layer:
        errors.append("required_layer must be a non-empty string")

    raw_records = document.get("records")
    if not isinstance(raw_records, list) or not raw_records:
        return HistoricalArtifactValidation(False, ("records must be non-empty",))

    computed_available = False
    for index, record in enumerate(raw_records):
        prefix = f"records[{index}]"
        if not isinstance(record, Mapping):
            errors.append(f"{prefix} must be an object")
            continue
        head_sha = record.get("head_sha")
        if not _hex(head_sha, 40):
            errors.append(f"{prefix}.head_sha is invalid")
            continue
        exact = head_sha == frozen_commit
        if record.get("exact_frozen_source") is not exact:
            errors.append(f"{prefix}.exact_frozen_source is inconsistent")

        conclusion = record.get("run_conclusion")
        jobs_executed = record.get("jobs_executed") is True
        contains_required = record.get("contains_required_layer") is True
        artifact_path = record.get("artifact_path")
        artifact_sha = record.get("artifact_sha256")
        artifact_valid = False

        if artifact_path is None:
            if artifact_sha is not None:
                errors.append(f"{prefix} has an artifact hash without a path")
        elif not isinstance(artifact_path, str) or not artifact_path:
            errors.append(f"{prefix}.artifact_path is invalid")
        else:
            candidate = (root / artifact_path).resolve()
            try:
                candidate.relative_to(root.resolve())
            except ValueError:
                errors.append(f"{prefix}.artifact_path escapes repository")
            else:
                if not candidate.is_file():
                    errors.append(f"{prefix} artifact is missing")
                elif not _hex(artifact_sha, 64):
                    errors.append(f"{prefix}.artifact_sha256 is invalid")
                elif _sha256(candidate) != artifact_sha:
                    errors.append(f"{prefix} artifact SHA-256 mismatch")
                else:
                    artifact_valid = True

        admissible = (
            exact
            and conclusion == "success"
            and jobs_executed
            and contains_required
            and artifact_valid
        )
        if record.get("admissible_for_frozen_source") is not admissible:
            errors.append(f"{prefix}.admissible_for_frozen_source is inconsistent")

        closes = record.get("closes_assumptions")
        if not isinstance(closes, list):
            errors.append(f"{prefix}.closes_assumptions must be a list")
        elif closes and not admissible:
            errors.append(f"{prefix} cannot close assumptions with inadmissible evidence")

        computed_available = computed_available or admissible

    if document.get("frozen_required_artifact_available") is not computed_available:
        errors.append("frozen_required_artifact_available is inconsistent")

    return HistoricalArtifactValidation(not errors, tuple(errors))
