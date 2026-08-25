"""Check that formal documents carry the current revalidation boundary."""

from __future__ import annotations

from dataclasses import dataclass
from pathlib import Path
from typing import Iterable

REVALIDATION_MARKER = "assumption revalidation"
FORBIDDEN_UNQUALIFIED = (
    "the production protocol is proven secure",
    "the implementation is proven constant-time",
    "all remaining assurance obligations are closed",
)


@dataclass(frozen=True)
class DocumentClaimValidation:
    valid: bool
    errors: tuple[str, ...]


def validate_formal_documents(paths: Iterable[Path]) -> DocumentClaimValidation:
    errors: list[str] = []
    seen = 0
    for path in paths:
        seen += 1
        text = path.read_text(encoding="utf-8")
        lowered = text.lower()
        if REVALIDATION_MARKER not in lowered:
            errors.append(f"{path}: missing current assumption revalidation section")
        for forbidden in FORBIDDEN_UNQUALIFIED:
            if forbidden in lowered:
                errors.append(f"{path}: unqualified production claim: {forbidden}")
    if seen == 0:
        errors.append("no formal documents supplied")
    return DocumentClaimValidation(not errors, tuple(errors))
