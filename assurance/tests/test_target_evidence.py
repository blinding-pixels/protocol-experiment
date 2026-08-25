from __future__ import annotations

import hashlib
import tempfile
import unittest
from pathlib import Path

from assurance.target_evidence import (
    supports_exact_target,
    validate_target_bound_measurement,
)


def target(architecture: str = "x86_64") -> dict[str, str]:
    return {
        "target_triple": f"{architecture}-unknown-linux-gnu",
        "operating_system": "Linux",
        "os_release": "test",
        "architecture": architecture,
        "cpu_model": "test-cpu",
        "compiler": "rustc test",
        "optimization_profile": "release",
    }


class TargetEvidenceTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.artifact = self.root / "samples.csv"
        self.artifact.write_text("sample,nanos\n0,1\n", encoding="utf-8")
        self.artifact_hash = hashlib.sha256(self.artifact.read_bytes()).hexdigest()
        self.binary = {
            "binary_sha256": "a" * 64,
            "source_commit": "b" * 40,
            "source_tree_sha256": "c" * 64,
            "target": target(),
        }
        self.record = {
            "schema": "causal-dag-assurance.target-measurement.v1",
            **self.binary,
            "artifact_path": "samples.csv",
            "artifact_sha256": self.artifact_hash,
        }

    def tearDown(self) -> None:
        self.temp.cleanup()

    def test_exact_binary_and_target_pass(self) -> None:
        result = validate_target_bound_measurement(
            self.record, self.binary, root=self.root
        )
        self.assertTrue(result.valid, result.errors)

    def test_cross_target_inference_is_forbidden(self) -> None:
        self.assertFalse(supports_exact_target(self.record, target("aarch64")))
        self.assertTrue(supports_exact_target(self.record, target()))

    def test_binary_hash_drift_is_rejected(self) -> None:
        self.record["binary_sha256"] = "d" * 64
        result = validate_target_bound_measurement(
            self.record, self.binary, root=self.root
        )
        self.assertFalse(result.valid)
        self.assertIn(
            "measurement binary_sha256 does not match the binary manifest",
            result.errors,
        )

    def test_source_commit_drift_is_rejected(self) -> None:
        self.record["source_commit"] = "e" * 40
        result = validate_target_bound_measurement(
            self.record, self.binary, root=self.root
        )
        self.assertFalse(result.valid)
        self.assertIn(
            "measurement source_commit does not match the binary manifest",
            result.errors,
        )

    def test_artifact_hash_drift_is_rejected(self) -> None:
        self.artifact.write_text("changed\n", encoding="utf-8")
        result = validate_target_bound_measurement(
            self.record, self.binary, root=self.root
        )
        self.assertFalse(result.valid)
        self.assertIn("measurement artifact SHA-256 mismatch", result.errors)

    def test_target_drift_is_rejected(self) -> None:
        self.record["target"] = target("aarch64")
        result = validate_target_bound_measurement(
            self.record, self.binary, root=self.root
        )
        self.assertFalse(result.valid)
        self.assertIn(
            "measurement target does not exactly match the binary target",
            result.errors,
        )


if __name__ == "__main__":
    unittest.main()
