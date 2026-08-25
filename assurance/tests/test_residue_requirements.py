from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from assurance.residue_requirements import validate_residue_requirements

ROOT = Path(__file__).resolve().parents[2]


class ResidueRequirementTests(unittest.TestCase):
    def document(self):
        return json.loads(
            (ROOT / "assurance/deployment_residue_requirements.json").read_text(
                encoding="utf-8"
            )
        )

    def test_all_unresolved_findings_are_honest_and_valid(self) -> None:
        result = validate_residue_requirements(self.document())
        self.assertTrue(result.valid, result.errors)

    def test_assumed_status_is_rejected(self) -> None:
        value = self.document()
        value["requirements"][0]["status"] = "assumed-safe"
        result = validate_residue_requirements(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("not 'assumed-safe'" in error for error in result.errors))

    def test_enforced_requires_load_bearing_negative_control(self) -> None:
        value = self.document()
        first = value["requirements"][0]
        first["status"] = "enforced"
        first["evidence"] = [
            {"type": "documentation", "sha256": "a" * 64, "negative_control_observed": True}
        ]
        result = validate_residue_requirements(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("lacks host/integration evidence" in error for error in result.errors))

    def test_missing_requirement_is_rejected(self) -> None:
        value = copy.deepcopy(self.document())
        value["requirements"].pop()
        result = validate_residue_requirements(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("shutdown-and-restart-erasure" in error for error in result.errors))


if __name__ == "__main__":
    unittest.main()
