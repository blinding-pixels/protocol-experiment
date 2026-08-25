"""Keep prototype evidence separate from production-integration obligations."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

REQUIRED_INTEGRATION_OBLIGATIONS = {
    "retention",
    "erasure",
    "audit-persistence",
    "revocation-propagation",
    "rollback-state",
    "capability-grant-active-member",
    "removal-rejoin-authority",
}
ALLOWED_CLOSURE_EVIDENCE = {"integration-test", "production-trace"}


@dataclass(frozen=True)
class ObligationValidation:
    valid: bool
    errors: tuple[str, ...]


def _hex64(value: object) -> bool:
    return (
        isinstance(value, str)
        and len(value) == 64
        and all(character in "0123456789abcdef" for character in value)
    )


def validate_integration_obligations(document: Mapping[str, Any]) -> ObligationValidation:
    errors: list[str] = []
    if document.get("schema") != "causal-dag-assurance.integration-obligations.v1":
        errors.append("unexpected integration-obligation schema")
    raw = document.get("obligations")
    if not isinstance(raw, list):
        return ObligationValidation(False, ("obligations must be a list",))
    ids: set[str] = set()
    for item in raw:
        if not isinstance(item, Mapping):
            errors.append("obligation must be an object")
            continue
        obligation_id = item.get("id")
        if not isinstance(obligation_id, str) or not obligation_id:
            errors.append("obligation has no id")
            continue
        if obligation_id in ids:
            errors.append(f"duplicate obligation: {obligation_id}")
        ids.add(obligation_id)
        if item.get("scope") != "production-integration":
            errors.append(f"{obligation_id}: scope must be production-integration")
        status = item.get("status")
        if status not in {"open", "verified"}:
            errors.append(f"{obligation_id}: invalid status {status!r}")
        evidence = item.get("evidence", [])
        if not isinstance(evidence, list):
            errors.append(f"{obligation_id}: evidence must be a list")
            continue
        if status == "verified":
            allowed = [
                record
                for record in evidence
                if isinstance(record, Mapping)
                and record.get("type") in ALLOWED_CLOSURE_EVIDENCE
                and _hex64(record.get("sha256"))
                and record.get("negative_control_observed") is True
            ]
            if not allowed:
                errors.append(
                    f"{obligation_id}: prototype tests, documents, models, or summary booleans cannot close a production obligation"
                )
    missing = REQUIRED_INTEGRATION_OBLIGATIONS - ids
    extra = ids - REQUIRED_INTEGRATION_OBLIGATIONS
    if missing:
        errors.append(f"missing integration obligations: {sorted(missing)}")
    if extra:
        errors.append(f"unexpected integration obligations: {sorted(extra)}")
    return ObligationValidation(not errors, tuple(errors))
