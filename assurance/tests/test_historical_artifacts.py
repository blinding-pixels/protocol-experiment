from __future__ import annotations

import copy
import json
import unittest
from pathlib import Path

from assurance.historical_artifacts import validate_historical_artifact_boundary

ROOT = Path(__file__).resolve().parents[2]
BOUNDARY = ROOT / "evidence/historical-artifact-boundary.json"


class HistoricalArtifactTests(unittest.TestCase):
    def document(self):
        return json.loads(BOUNDARY.read_text(encoding="utf-8"))

    def test_repository_boundary_passes(self) -> None:
        result = validate_historical_artifact_boundary(self.document(), root=ROOT)
        self.assertTrue(result.valid, result.errors)

    def test_stale_success_cannot_be_admissible(self) -> None:
        value = self.document()
        value["records"][0]["admissible_for_frozen_source"] = True
        result = validate_historical_artifact_boundary(value, root=ROOT)
        self.assertFalse(result.valid)
        self.assertTrue(
            any("admissible_for_frozen_source is inconsistent" in error for error in result.errors)
        )

    def test_exact_but_unexecuted_run_cannot_be_admissible(self) -> None:
        value = self.document()
        value["records"][3]["admissible_for_frozen_source"] = True
        result = validate_historical_artifact_boundary(value, root=ROOT)
        self.assertFalse(result.valid)

    def test_inadmissible_artifact_cannot_close_an_assumption(self) -> None:
        value = self.document()
        value["records"][1]["closes_assumptions"] = ["A-002"]
        result = validate_historical_artifact_boundary(value, root=ROOT)
        self.assertFalse(result.valid)
        self.assertTrue(any("cannot close assumptions" in error for error in result.errors))

    def test_artifact_hash_drift_is_rejected(self) -> None:
        value = copy.deepcopy(self.document())
        value["records"][0]["artifact_sha256"] = "f" * 64
        result = validate_historical_artifact_boundary(value, root=ROOT)
        self.assertFalse(result.valid)
        self.assertTrue(any("artifact SHA-256 mismatch" in error for error in result.errors))


if __name__ == "__main__":
    unittest.main()
