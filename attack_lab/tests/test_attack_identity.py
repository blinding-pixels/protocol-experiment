from __future__ import annotations

import copy
import unittest

from attack_lab.attack_identity import compare_attack_identity
from attack_lab.pair_validation import validate_protocol_pair, validate_timing_pair

HEX_A = "a" * 64
HEX_B = "b" * 64
HEX_C = "c" * 64
COMMIT = "1" * 40
TREE = "2" * 64


def result(variant: str, binary_hash: str) -> dict[str, object]:
    identity = {
        "variant": variant,
        "path": f"/tmp/{variant}",
        "sha256": binary_hash,
        "size": 1234,
        "source_commit": COMMIT,
        "source_tree_sha256": TREE,
        "broken_feature_count": 0 if variant == "correct" else 1,
    }
    return {
        "schema": "facets.cdg.attack-lab.v1",
        "scenario": "unauthorized-operation",
        "layer": "protocol-logic",
        "variant": variant,
        "source_commit": COMMIT,
        "attack_input_digest": HEX_A,
        "execution_provenance": {
            "verified_before": copy.deepcopy(identity),
            "verified_after": copy.deepcopy(identity),
            "same_binary_identity_through_execution": True,
        },
    }


class AttackIdentityTests(unittest.TestCase):
    def setUp(self) -> None:
        self.correct = result("correct", HEX_B)
        self.broken = result("broken-role-gate", HEX_C)

    def compare(self):
        return validate_protocol_pair(
            "unauthorized-operation", "broken-role-gate", self.correct, self.broken
        )

    def test_valid_pair_is_conjunctive(self) -> None:
        comparison = self.compare()
        self.assertTrue(comparison.valid, comparison.errors)
        self.assertEqual(comparison.compared_digest_fields, ("attack_input_digest",))
        self.assertEqual(comparison.source_tree_sha256, TREE)

    def test_first_digest_equal_later_digest_different_is_rejected(self) -> None:
        self.correct["transcript_digest"] = HEX_A
        self.broken["transcript_digest"] = HEX_B
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertIn("transcript_digest mismatch", comparison.errors)
        self.assertEqual(
            comparison.compared_digest_fields,
            ("attack_input_digest", "transcript_digest"),
        )

    def test_digest_present_on_only_one_side_is_rejected(self) -> None:
        self.correct["transcript_digest"] = HEX_A
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertIn("transcript_digest is present on only one result", comparison.errors)

    def test_no_digest_is_rejected(self) -> None:
        del self.correct["attack_input_digest"]
        del self.broken["attack_input_digest"]
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertIn("no attack-input or transcript digest was compared", comparison.errors)

    def test_scenario_mismatch_is_rejected(self) -> None:
        self.broken["scenario"] = "unauthorized-fork"
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertTrue(any(error.startswith("scenario mismatch") for error in comparison.errors))

    def test_layer_mismatch_is_rejected(self) -> None:
        self.broken["layer"] = "protocol-accountability"
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertTrue(any(error.startswith("layer mismatch") for error in comparison.errors))

    def test_source_commit_mismatch_is_rejected(self) -> None:
        self.broken["source_commit"] = "3" * 40
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertTrue(
            any(error.startswith("source_commit mismatch") for error in comparison.errors)
        )

    def test_source_tree_mismatch_is_rejected(self) -> None:
        provenance = self.broken["execution_provenance"]
        assert isinstance(provenance, dict)
        for key in ("verified_before", "verified_after"):
            value = provenance[key]
            assert isinstance(value, dict)
            value["source_tree_sha256"] = "4" * 64
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertIn("verified source_tree_sha256 mismatch", comparison.errors)

    def test_binary_replacement_during_execution_is_rejected(self) -> None:
        provenance = self.broken["execution_provenance"]
        assert isinstance(provenance, dict)
        after = provenance["verified_after"]
        assert isinstance(after, dict)
        after["sha256"] = "5" * 64
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertIn("right sha256 changed during execution", comparison.errors)

    def test_identical_binary_bytes_are_rejected(self) -> None:
        provenance = self.broken["execution_provenance"]
        assert isinstance(provenance, dict)
        for key in ("verified_before", "verified_after"):
            value = provenance[key]
            assert isinstance(value, dict)
            value["sha256"] = HEX_B
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertIn(
            "dual-target comparison resolved to identical binary bytes",
            comparison.errors,
        )

    def test_invalid_digest_format_is_rejected(self) -> None:
        self.broken["attack_input_digest"] = "not-a-digest"
        comparison = self.compare()
        self.assertFalse(comparison.valid)
        self.assertIn(
            "right attack_input_digest is not a 64-character lowercase hex digest",
            comparison.errors,
        )

    def test_timing_pair_requires_all_public_measurement_inputs(self) -> None:
        correct = result("correct", HEX_B)
        broken = result("broken-trial-decryption", HEX_C)
        for item in (correct, broken):
            item.update(
                {
                    "scenario": "retained-secret-selection",
                    "layer": "binary-timing",
                    "public_selector": "f" * 32,
                    "samples": 4000,
                    "kappa": 32,
                    "payload_size": 4096,
                    "classification_target": "retained-secret-slot-not-public-selector",
                }
            )
        self.assertTrue(validate_timing_pair(correct, broken).valid)
        broken["samples"] = 3999
        comparison = validate_timing_pair(correct, broken)
        self.assertFalse(comparison.valid)
        self.assertIn("samples mismatch: 4000 != 3999", comparison.errors)

    def test_low_level_comparator_can_require_an_extra_field(self) -> None:
        self.correct["fixture_version"] = 1
        self.broken["fixture_version"] = 2
        comparison = compare_attack_identity(
            self.correct,
            self.broken,
            additional_equal_fields=("fixture_version",),
        )
        self.assertFalse(comparison.valid)
        self.assertIn("fixture_version mismatch: 1 != 2", comparison.errors)


if __name__ == "__main__":
    unittest.main()
