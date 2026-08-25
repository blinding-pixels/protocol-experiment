"""Validate that formal claim prose cannot outrun the claim matrix."""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any, Mapping

ALLOWED_STATUS = {
    "conditional-holds",
    "does-not-hold-as-stated",
    "open",
}


@dataclass(frozen=True)
class ClaimStatusValidation:
    valid: bool
    errors: tuple[str, ...]


def validate_claim_status(
    document: Mapping[str, Any], *, assumption_ids: set[str]
) -> ClaimStatusValidation:
    errors: list[str] = []
    if document.get("schema") != "causal-dag-assurance.formal-claim-status.v1":
        errors.append("unexpected formal claim-status schema")
    claims = document.get("claims")
    if not isinstance(claims, list) or not claims:
        return ClaimStatusValidation(False, ("claims must be a non-empty list",))
    seen: set[str] = set()
    for claim in claims:
        if not isinstance(claim, Mapping):
            errors.append("claim must be an object")
            continue
        claim_id = claim.get("id")
        if not isinstance(claim_id, str) or not claim_id:
            errors.append("claim has no id")
            continue
        if claim_id in seen:
            errors.append(f"duplicate claim id: {claim_id}")
        seen.add(claim_id)
        status = claim.get("status")
        model_result = claim.get("model_result")
        if status not in ALLOWED_STATUS:
            errors.append(f"{claim_id}: invalid status {status!r}")
        dependencies = claim.get("assumption_dependencies")
        if not isinstance(dependencies, list):
            errors.append(f"{claim_id}: assumption_dependencies must be a list")
        else:
            unknown = [item for item in dependencies if item not in assumption_ids]
            if unknown:
                errors.append(f"{claim_id}: unknown assumptions {sorted(unknown)}")
        if model_result == "counterexample-observed" and status != "does-not-hold-as-stated":
            errors.append(
                f"{claim_id}: counterexample-observed cannot be declared holding"
            )
        if model_result == "not-executed-current-source" and status != "open":
            errors.append(
                f"{claim_id}: unexecuted current-source claim must remain open"
            )
        if claim.get("layer") in {"implementation", "production", "measurement"}:
            if status != "open":
                errors.append(f"{claim_id}: unexecuted concrete-layer claim must remain open")
    return ClaimStatusValidation(not errors, tuple(errors))
