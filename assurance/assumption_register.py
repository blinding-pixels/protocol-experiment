"""Reject assumption closure based on prose, unchecked booleans, or stale files."""

from __future__ import annotations

import hashlib
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

ALLOWED_STATUSES = {
    "open",
    "implemented-pending-execution",
    "implemented-pending-integration",
    "verified",
}
LOAD_BEARING_EVIDENCE = {
    "source",
    "test-report",
    "compiled-execution",
    "measurement",
    "integration-test",
    "production-trace",
}


@dataclass(frozen=True)
class AssumptionRegisterValidation:
    valid: bool
    errors: tuple[str, ...]


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _hex64(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def validate_assumption_register(
    document: Mapping[str, Any], *, root: Path
) -> AssumptionRegisterValidation:
    errors: list[str] = []
    if document.get("schema") != "causal-dag-assurance.assumption-register.v1":
        errors.append("unexpected assumption-register schema")
    raw = document.get("assumptions")
    if not isinstance(raw, list) or not raw:
        return AssumptionRegisterValidation(False, ("assumptions must be non-empty",))
    ids: set[str] = set()
    for item in raw:
        if not isinstance(item, Mapping):
            errors.append("assumption must be an object")
            continue
        assumption_id = item.get("id")
        if not isinstance(assumption_id, str) or not assumption_id:
            errors.append("assumption has no id")
            continue
        if assumption_id in ids:
            errors.append(f"duplicate assumption id: {assumption_id}")
        ids.add(assumption_id)
        status = item.get("status")
        if status not in ALLOWED_STATUSES:
            errors.append(f"{assumption_id}: invalid status {status!r}")
        evidence = item.get("evidence", [])
        if not isinstance(evidence, list):
            errors.append(f"{assumption_id}: evidence must be a list")
            continue
        valid_records: list[Mapping[str, Any]] = []
        for record in evidence:
            if not isinstance(record, Mapping):
                errors.append(f"{assumption_id}: evidence record must be an object")
                continue
            relative = record.get("path")
            expected = record.get("sha256")
            if not isinstance(relative, str) or not relative:
                errors.append(f"{assumption_id}: evidence path is missing")
                continue
            path = (root / relative).resolve()
            try:
                path.relative_to(root.resolve())
            except ValueError:
                errors.append(f"{assumption_id}: evidence path escapes repository")
                continue
            if not path.is_file():
                errors.append(f"{assumption_id}: missing evidence file {relative}")
                continue
            if not _hex64(expected) or _sha256(path) != expected:
                errors.append(f"{assumption_id}: stale evidence hash for {relative}")
                continue
            valid_records.append(record)
        if status == "verified":
            load_bearing = [
                record
                for record in valid_records
                if record.get("type") in LOAD_BEARING_EVIDENCE
            ]
            if not load_bearing:
                errors.append(
                    f"{assumption_id}: verified status has no load-bearing artifact"
                )
            if not any(
                record.get("negative_control_observed") is True
                for record in load_bearing
            ):
                errors.append(
                    f"{assumption_id}: verified status has no observed negative control"
                )
    return AssumptionRegisterValidation(not errors, tuple(errors))
