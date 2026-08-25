"""Frozen weak comparator from the Facets checkpoint; retained as a negative control."""

from typing import Any


def shared_attack_input(correct: dict[str, Any], broken: dict[str, Any]) -> bool:
    for field in ("attack_input_digest", "transcript_digest"):
        if field in correct or field in broken:
            return correct.get(field) == broken.get(field)
    return False
