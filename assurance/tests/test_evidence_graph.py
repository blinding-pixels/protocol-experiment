from __future__ import annotations

import copy
import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from assurance.evidence_graph import validate_evidence_graph

COMMIT = "1" * 40
TREE = "2" * 64


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def target() -> dict[str, str]:
    return {
        "target_triple": "x86_64-unknown-linux-gnu",
        "operating_system": "Linux",
        "os_release": "test",
        "architecture": "x86_64",
        "cpu_model": "test-cpu",
        "compiler": "rustc test",
        "optimization_profile": "release",
    }


class EvidenceGraphTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.source = self.root / "protocol.rs"
        self.source.write_text(
            "pub struct CausalStateCommitment {\n    field: u32,\n}\n",
            encoding="utf-8",
        )
        self.binary = self.root / "attack-lab"
        self.binary.write_bytes(b"compiled-binary-bytes")
        self.metadata = self.root / "attack-lab.metadata.json"
        self.metadata.write_text(
            json.dumps(
                {
                    "binary_sha256": sha(self.binary),
                    "source_commit": COMMIT,
                    "source_tree_sha256": TREE,
                }
            ),
            encoding="utf-8",
        )
        self.measurement = self.root / "samples.csv"
        self.measurement.write_text("sample,nanos\n0,10\n", encoding="utf-8")
        self.negative = self.root / "negative.json"
        self.negative.write_text(
            json.dumps(
                {
                    "expected_failure_observed": True,
                    "failure_reason": "stale digest was rejected",
                }
            ),
            encoding="utf-8",
        )
        self.docs = self.root / "README.md"
        self.docs.write_text("claim prose\n", encoding="utf-8")
        self.graph_path = self.root / "EVIDENCE_GRAPH.json"
        self.document = {
            "schema": "causal-dag-assurance.evidence-graph.v2",
            "nodes": [
                {
                    "id": "source:protocol",
                    "kind": "source",
                    "path": "protocol.rs",
                    "sha256": sha(self.source),
                    "declarations": [
                        {
                            "pattern": r"^pub struct CausalStateCommitment \{$",
                            "count": 1,
                        }
                    ],
                    "depends_on": [],
                },
                {
                    "id": "binary:correct",
                    "kind": "binary",
                    "path": "attack-lab",
                    "sha256": sha(self.binary),
                    "metadata_path": "attack-lab.metadata.json",
                    "metadata_sha256": sha(self.metadata),
                    "source_commit": COMMIT,
                    "source_tree_sha256": TREE,
                    "target": target(),
                    "depends_on": ["source:protocol"],
                },
                {
                    "id": "measurement:timing",
                    "kind": "measurement",
                    "schema": "causal-dag-assurance.target-measurement.v1",
                    "path": "samples.csv",
                    "sha256": sha(self.measurement),
                    "binary_node": "binary:correct",
                    "binary_sha256": sha(self.binary),
                    "source_commit": COMMIT,
                    "source_tree_sha256": TREE,
                    "target": target(),
                    "depends_on": ["binary:correct"],
                },
                {
                    "id": "negative:stale-digest",
                    "kind": "negative_control",
                    "path": "negative.json",
                    "sha256": sha(self.negative),
                    "depends_on": ["source:protocol"],
                },
                {
                    "id": "doc:readme",
                    "kind": "documentation",
                    "path": "README.md",
                    "sha256": sha(self.docs),
                    "depends_on": [],
                },
            ],
            "claims": [
                {
                    "id": "exact-binary-timing",
                    "status": "verified",
                    "evidence": [
                        "source:protocol",
                        "binary:correct",
                        "measurement:timing",
                        "negative:stale-digest",
                    ],
                }
            ],
        }
        self.graph_path.write_text(
            json.dumps(self.document, indent=2), encoding="utf-8"
        )

    def tearDown(self) -> None:
        self.temp.cleanup()

    def validate(self, document=None):
        return validate_evidence_graph(
            document or self.document,
            root=self.root,
            graph_path=self.graph_path,
        )

    def test_valid_graph_passes(self) -> None:
        result = self.validate()
        self.assertTrue(result.valid, result.errors)

    def test_stale_file_hash_is_rejected(self) -> None:
        value = copy.deepcopy(self.document)
        value["nodes"][0]["sha256"] = "f" * 64
        result = self.validate(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("stale or incorrect" in error for error in result.errors))

    def test_loose_substring_pattern_is_rejected(self) -> None:
        value = copy.deepcopy(self.document)
        value["nodes"][0]["declarations"][0]["pattern"] = "CausalStateCommitment"
        result = self.validate(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("line-anchored" in error for error in result.errors))

    def test_missing_exact_declaration_is_rejected(self) -> None:
        value = copy.deepcopy(self.document)
        value["nodes"][0]["declarations"][0]["pattern"] = r"^pub struct Missing \{$"
        result = self.validate(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("declaration count" in error for error in result.errors))

    def test_dependency_cycle_is_rejected(self) -> None:
        value = copy.deepcopy(self.document)
        value["nodes"][0]["depends_on"] = ["binary:correct"]
        result = self.validate(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("dependency cycle" in error for error in result.errors))

    def test_graph_cannot_attest_to_itself(self) -> None:
        value = copy.deepcopy(self.document)
        value["nodes"].append(
            {
                "id": "self:graph",
                "kind": "documentation",
                "path": "EVIDENCE_GRAPH.json",
                "sha256": sha(self.graph_path),
                "depends_on": [],
            }
        )
        result = self.validate(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("cannot attest to itself" in error for error in result.errors))

    def test_documentation_alone_cannot_verify_claim(self) -> None:
        value = copy.deepcopy(self.document)
        value["claims"][0]["evidence"] = ["doc:readme"]
        result = self.validate(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("sole verification" in error for error in result.errors))

    def test_verified_claim_requires_negative_control(self) -> None:
        value = copy.deepcopy(self.document)
        value["claims"][0]["evidence"] = [
            "source:protocol",
            "binary:correct",
            "measurement:timing",
        ]
        result = self.validate(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("no load-bearing negative control" in error for error in result.errors))

    def test_measurement_must_bind_exact_binary_hash(self) -> None:
        value = copy.deepcopy(self.document)
        measurement = next(
            node for node in value["nodes"] if node["id"] == "measurement:timing"
        )
        measurement["binary_sha256"] = "e" * 64
        result = self.validate(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("binary_sha256" in error for error in result.errors))

    def test_binary_metadata_must_bind_actual_binary(self) -> None:
        metadata = json.loads(self.metadata.read_text(encoding="utf-8"))
        metadata["binary_sha256"] = "d" * 64
        self.metadata.write_text(json.dumps(metadata), encoding="utf-8")
        value = copy.deepcopy(self.document)
        binary = next(node for node in value["nodes"] if node["id"] == "binary:correct")
        binary["metadata_sha256"] = sha(self.metadata)
        result = self.validate(value)
        self.assertFalse(result.valid)
        self.assertTrue(any("metadata binary_sha256 mismatch" in error for error in result.errors))


if __name__ == "__main__":
    unittest.main()
