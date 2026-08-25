"""Turn host-residue assumptions into enforced controls or unresolved findings."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

REQUIRED_REQUIREMENTS = {
    "swap-and-hibernation",
    "core-dumps-and-crash-reports",
    "allocator-reuse",
    "temporary-files",
    "logs-and-telemetry",
    "backups-and-snapshots",
    "process-memory-access",
    "shutdown-and-restart-erasure",
}
ALLOWED_ENFORCEMENT_EVIDENCE = {"host-policy-test", "integration-test", "production-trace"}


@dataclass(frozen=True)
class ResidueValidation:
    valid: bool
    errors: tuple[str, ...]


def _hex64(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def validate_residue_requirements(document: Mapping[str, Any]) -> ResidueValidation:
    errors: list[str] = []
    if document.get("schema") != "causal-dag-assurance.residue-requirements.v1":
        errors.append("unexpected residue-requirement schema")
    raw = document.get("requirements")
    if not isinstance(raw, list):
        return ResidueValidation(False, ("requirements must be a list",))
    ids: set[str] = set()
    for item in raw:
        if not isinstance(item, Mapping):
            errors.append("residue requirement must be an object")
            continue
        requirement_id = item.get("id")
        if not isinstance(requirement_id, str) or not requirement_id:
            errors.append("residue requirement has no id")
            continue
        if requirement_id in ids:
            errors.append(f"duplicate residue requirement: {requirement_id}")
        ids.add(requirement_id)
        status = item.get("status")
        if status not in {"unresolved", "enforced"}:
            errors.append(
                f"{requirement_id}: status must be unresolved or enforced, not {status!r}"
            )
        finding = item.get("finding")
        if not isinstance(finding, str) or not finding:
            errors.append(f"{requirement_id}: finding must be explicit")
        evidence = item.get("evidence", [])
        if not isinstance(evidence, list):
            errors.append(f"{requirement_id}: evidence must be a list")
            continue
        if status == "enforced":
            valid = [
                record
                for record in evidence
                if isinstance(record, Mapping)
                and record.get("type") in ALLOWED_ENFORCEMENT_EVIDENCE
                and _hex64(record.get("sha256"))
                and record.get("negative_control_observed") is True
            ]
            if not valid:
                errors.append(
                    f"{requirement_id}: enforced status lacks host/integration evidence with a negative control"
                )
    missing = REQUIRED_REQUIREMENTS - ids
    extra = ids - REQUIRED_REQUIREMENTS
    if missing:
        errors.append(f"missing residue requirements: {sorted(missing)}")
    if extra:
        errors.append(f"unexpected residue requirements: {sorted(extra)}")
    return ResidueValidation(not errors, tuple(errors))
