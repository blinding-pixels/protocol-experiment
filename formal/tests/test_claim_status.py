from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from formal.claim_status import validate_claim_status

ROOT = Path(__file__).resolve().parents[2]


def matrix() -> dict[str, object]:
    return json.loads((ROOT / "formal/FORMAL_CLAIM_STATUS.json").read_text(encoding="utf-8"))


def assumption_ids() -> set[str]:
    register = json.loads((ROOT / "ASSUMPTION_REGISTER.json").read_text(encoding="utf-8"))
    return {item["id"] for item in register["assumptions"]}


class ClaimStatusTests(unittest.TestCase):
    def test_repository_matrix_passes(self) -> None:
        result = validate_claim_status(matrix(), assumption_ids=assumption_ids())
        self.assertTrue(result.valid, result.errors)

    def test_lifecycle_counterexample_cannot_be_declared_holding(self) -> None:
        value = copy.deepcopy(matrix())
        claim = next(item for item in value["claims"] if item["id"] == "C-007")
        claim["status"] = "conditional-holds"
        result = validate_claim_status(value, assumption_ids=assumption_ids())
        self.assertFalse(result.valid)

    def test_open_execution_dependency_cannot_be_declared_closed(self) -> None:
        value = copy.deepcopy(matrix())
        claim = next(item for item in value["claims"] if item["id"] == "C-009")
        claim["status"] = "conditional-holds"
        result = validate_claim_status(value, assumption_ids=assumption_ids())
        self.assertFalse(result.valid)

    def test_unknown_assumption_is_rejected(self) -> None:
        value = copy.deepcopy(matrix())
        value["claims"][0]["assumption_dependencies"].append("A-999-invented")
        result = validate_claim_status(value, assumption_ids=assumption_ids())
        self.assertFalse(result.valid)


if __name__ == "__main__":
    unittest.main()
