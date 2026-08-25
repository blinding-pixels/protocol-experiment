"""Drop-in pair validators for batch and interactive attack-lab callers."""

from __future__ import annotations

from typing import Any, Mapping

from .attack_identity import AttackIdentityComparison, compare_attack_identity


def validate_protocol_pair(
    scenario: str,
    broken_variant: str,
    correct: Mapping[str, Any],
    broken: Mapping[str, Any],
) -> AttackIdentityComparison:
    expected_layer = (
        "protocol-accountability"
        if scenario == "receipt-equivocation"
        else "protocol-logic"
    )
    return compare_attack_identity(
        correct,
        broken,
        expected_scenario=scenario,
        expected_layer=expected_layer,
        expected_left_variant="correct",
        expected_right_variant=broken_variant,
    )


def validate_timing_pair(
    correct: Mapping[str, Any], broken: Mapping[str, Any]
) -> AttackIdentityComparison:
    return compare_attack_identity(
        correct,
        broken,
        expected_scenario="retained-secret-selection",
        expected_layer="binary-timing",
        expected_left_variant="correct",
        expected_right_variant="broken-trial-decryption",
        additional_equal_fields=(
            "public_selector",
            "samples",
            "kappa",
            "payload_size",
            "classification_target",
        ),
    )
