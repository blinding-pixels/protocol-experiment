from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from formal.doc_claims import validate_formal_documents

ROOT = Path(__file__).resolve().parents[2]


class DocumentClaimTests(unittest.TestCase):
    def test_repository_documents_pass(self) -> None:
        documents = sorted((ROOT / "formal/documents").glob("*.md"))
        result = validate_formal_documents(documents)
        self.assertTrue(result.valid, result.errors)

    def test_missing_revalidation_section_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "claim.md"
            path.write_text("# Historical claim\n", encoding="utf-8")
            result = validate_formal_documents([path])
            self.assertFalse(result.valid)

    def test_unqualified_production_claim_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "claim.md"
            path.write_text(
                "# Claim\n\n## Assumption revalidation\n\n"
                "The production protocol is proven secure.\n",
                encoding="utf-8",
            )
            result = validate_formal_documents([path])
            self.assertFalse(result.valid)


if __name__ == "__main__":
    unittest.main()
