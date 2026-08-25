from __future__ import annotations

import copy
import unittest

from assurance.obligations import validate_integration_obligations


def document() -> dict[str, object]:
    return {
        "schema": "causal-dag-assurance.integration-obligations.v1",
        "obligations": [
            {
                "id": obligation_id,
                "scope": "production-integration",
                "status": "open",
                "evidence": [],
            }
            for obligation_id in (
                "retention",
                "erasure",
                "audit-persistence",
                "revocation-propagation",
                "rollback-state",
                "capability-grant-active-member",
                "removal-rejoin-authority",
            )
        ],
    }


class ObligationTests(unittest.TestCase):
    def test_explicit_open_register_passes(self) -> None:
        result = validate_integration_obligations(document())
        self.assertTrue(result.valid, result.errors)

    def test_documentation_cannot_close_production_obligation(self) -> None:
        value = document()
        obligations = value["obligations"]
        assert isinstance(obligations, list)
        first = obligations[0]
        assert isinstance(first, dict)
        first["status"] = "verified"
        first["evidence"] = [
            {"type": "documentation", "sha256": "a" * 64, "negative_control_observed": True}
        ]
        result = validate_integration_obligations(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("cannot close" in error for error in result.errors))

    def test_prototype_test_cannot_close_production_obligation(self) -> None:
        value = document()
        obligations = value["obligations"]
        assert isinstance(obligations, list)
        first = obligations[0]
        assert isinstance(first, dict)
        first["status"] = "verified"
        first["evidence"] = [
            {"type": "prototype-test", "sha256": "a" * 64, "negative_control_observed": True}
        ]
        result = validate_integration_obligations(value)
        self.assertFalse(result.valid)

    def test_integration_test_needs_negative_control(self) -> None:
        value = document()
        obligations = value["obligations"]
        assert isinstance(obligations, list)
        first = obligations[0]
        assert isinstance(first, dict)
        first["status"] = "verified"
        first["evidence"] = [
            {"type": "integration-test", "sha256": "a" * 64, "negative_control_observed": False}
        ]
        result = validate_integration_obligations(value)
        self.assertFalse(result.valid)

    def test_valid_integration_evidence_can_close_one_obligation(self) -> None:
        value = copy.deepcopy(document())
        obligations = value["obligations"]
        assert isinstance(obligations, list)
        first = obligations[0]
        assert isinstance(first, dict)
        first["status"] = "verified"
        first["evidence"] = [
            {"type": "integration-test", "sha256": "a" * 64, "negative_control_observed": True}
        ]
        result = validate_integration_obligations(value)
        self.assertTrue(result.valid, result.errors)

    def test_missing_rollback_obligation_is_rejected(self) -> None:
        value = document()
        obligations = value["obligations"]
        assert isinstance(obligations, list)
        obligations[:] = [item for item in obligations if item.get("id") != "rollback-state"]
        result = validate_integration_obligations(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("rollback-state" in error for error in result.errors))


if __name__ == "__main__":
    unittest.main()
