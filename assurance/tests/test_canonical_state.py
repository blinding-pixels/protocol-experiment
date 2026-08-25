from __future__ import annotations

import json
import unittest
from pathlib import Path

from assurance.canonical_state import (
    AUTHORIZATION_DOMAIN,
    CAUSAL_STATE_DOMAIN,
    Capability,
    CausalStateComponents,
    _context_id_with_domains,
    context_id,
)

ROOT = Path(__file__).resolve().parents[2]


def state(version: int = 1) -> CausalStateComponents:
    return CausalStateComponents(
        dag_root=bytes([10]) * 32,
        valid_forks_digest=bytes([11]) * 32,
        grants_digest=bytes([12]) * 32,
        punctures_digest=bytes([13]) * 32,
        policy_version=version,
    )


class CanonicalStateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.alice = bytes([1]) * 32
        self.bob = bytes([2]) * 32
        self.members = [self.alice, self.bob]
        self.capabilities = [
            (self.alice, Capability.MANAGE_GROUP),
            (self.bob, Capability.CREATE_FORK),
        ]

    def test_input_permutations_are_identical(self) -> None:
        left = context_id(state(), self.members, self.capabilities)
        right = context_id(
            state(), list(reversed(self.members)), list(reversed(self.capabilities))
        )
        self.assertEqual(left, right)

    def test_duplicates_are_normalized(self) -> None:
        baseline = context_id(state(), self.members, self.capabilities)
        duplicate = context_id(
            state(),
            self.members + [self.alice, self.bob],
            self.capabilities + [self.capabilities[0], self.capabilities[1]],
        )
        self.assertEqual(baseline, duplicate)

    def test_policy_version_change_changes_context(self) -> None:
        self.assertNotEqual(
            context_id(state(1), self.members, self.capabilities),
            context_id(state(2), self.members, self.capabilities),
        )

    def test_authorization_domain_change_changes_context(self) -> None:
        canonical = context_id(state(), self.members, self.capabilities)
        changed = _context_id_with_domains(
            state(),
            self.members,
            self.capabilities,
            authorization_domain=AUTHORIZATION_DOMAIN + b"-changed",
            causal_state_domain=CAUSAL_STATE_DOMAIN,
        )
        self.assertNotEqual(canonical, changed)

    def test_causal_state_domain_change_changes_context(self) -> None:
        canonical = context_id(state(), self.members, self.capabilities)
        changed = _context_id_with_domains(
            state(),
            self.members,
            self.capabilities,
            authorization_domain=AUTHORIZATION_DOMAIN,
            causal_state_domain=CAUSAL_STATE_DOMAIN + b"-changed",
        )
        self.assertNotEqual(canonical, changed)

    def test_component_position_is_bound(self) -> None:
        original = state()
        swapped = CausalStateComponents(
            dag_root=original.valid_forks_digest,
            valid_forks_digest=original.dag_root,
            grants_digest=original.grants_digest,
            punctures_digest=original.punctures_digest,
            policy_version=original.policy_version,
        )
        self.assertNotEqual(
            context_id(original, self.members, self.capabilities),
            context_id(swapped, self.members, self.capabilities),
        )

    def test_capability_code_is_bound(self) -> None:
        changed = [
            (self.alice, Capability.CREATE_FORK),
            (self.bob, Capability.MANAGE_GROUP),
        ]
        self.assertNotEqual(
            context_id(state(), self.members, self.capabilities),
            context_id(state(), self.members, changed),
        )

    def test_invalid_component_length_is_rejected(self) -> None:
        with self.assertRaises(ValueError):
            CausalStateComponents(
                dag_root=b"short",
                valid_forks_digest=bytes(32),
                grants_digest=bytes(32),
                punctures_digest=bytes(32),
                policy_version=1,
            )

    def test_frozen_vector(self) -> None:
        vector = json.loads(
            (ROOT / "assurance/canonical_state_vector.json").read_text(
                encoding="utf-8"
            )
        )
        observed = context_id(state(), self.members, self.capabilities).hex()
        self.assertEqual(observed, vector["context_id_sha256"])


if __name__ == "__main__":
    unittest.main()
