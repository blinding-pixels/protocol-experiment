from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from assurance.assumption_register import validate_assumption_register

ROOT = Path(__file__).resolve().parents[2]


class AssumptionRegisterTests(unittest.TestCase):
    def document(self):
        return json.loads((ROOT / "ASSUMPTION_REGISTER.json").read_text(encoding="utf-8"))

    def test_repository_register_passes(self) -> None:
        result = validate_assumption_register(self.document(), root=ROOT)
        self.assertTrue(result.valid, result.errors)

    def test_verified_status_rejects_document_only_evidence(self) -> None:
        value = self.document()
        assumption = value["assumptions"][0]
        assumption["evidence"] = [
            {
                "type": "documentation",
                "path": "README.md",
                "sha256": __import__("hashlib").sha256((ROOT / "README.md").read_bytes()).hexdigest(),
                "negative_control_observed": True,
            }
        ]
        result = validate_assumption_register(value, root=ROOT)
        self.assertFalse(result.valid)
        self.assertTrue(any("no load-bearing artifact" in error for error in result.errors))

    def test_verified_status_requires_negative_control(self) -> None:
        value = self.document()
        assumption = value["assumptions"][0]
        for record in assumption["evidence"]:
            record["negative_control_observed"] = False
        result = validate_assumption_register(value, root=ROOT)
        self.assertFalse(result.valid)
        self.assertTrue(any("no observed negative control" in error for error in result.errors))

    def test_stale_hash_is_rejected(self) -> None:
        value = self.document()
        value["assumptions"][0]["evidence"][0]["sha256"] = "f" * 64
        result = validate_assumption_register(value, root=ROOT)
        self.assertFalse(result.valid)
        self.assertTrue(any("stale evidence hash" in error for error in result.errors))

    def test_path_escape_is_rejected(self) -> None:
        value = self.document()
        value["assumptions"][0]["evidence"][0]["path"] = "../outside"
        result = validate_assumption_register(value, root=ROOT)
        self.assertFalse(result.valid)
        self.assertTrue(any("escapes repository" in error for error in result.errors))

    def test_unrecognized_closed_status_is_rejected(self) -> None:
        value = copy.deepcopy(self.document())
        value["assumptions"][1]["status"] = "closed-by-review"
        result = validate_assumption_register(value, root=ROOT)
        self.assertFalse(result.valid)
        self.assertTrue(any("invalid status" in error for error in result.errors))


if __name__ == "__main__":
    unittest.main()
