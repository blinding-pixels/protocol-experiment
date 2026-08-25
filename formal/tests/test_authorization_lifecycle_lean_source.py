from __future__ import annotations

import re
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
SOURCE = ROOT / "formal/current-source/CausalDagCgka/AuthorizationLifecycle.lean"
MAIN = ROOT / "formal/current-source/CausalDagCgka/Main.lean"
README = ROOT / "formal/current-source/README.md"


class AuthorizationLifecycleLeanSourceTests(unittest.TestCase):
    def test_current_source_exists_and_is_imported(self) -> None:
        self.assertTrue(SOURCE.is_file())
        main = MAIN.read_text(encoding="utf-8")
        self.assertIn("CausalDagCgka.AuthorizationLifecycle", main)

    def test_lifecycle_source_has_no_placeholder_or_new_axiom(self) -> None:
        text = SOURCE.read_text(encoding="utf-8")
        for forbidden in ("sorry", "admit", "sorryAx", "axiom "):
            self.assertNotIn(forbidden, text)

    def test_lifecycle_source_imports_only_existing_authorization_layer(self) -> None:
        imports = re.findall(r"^import\s+(.+)$", SOURCE.read_text(encoding="utf-8"), re.MULTILINE)
        self.assertEqual(imports, ["CausalDagCgka.Authorization"])

    def test_lifecycle_source_names_counterexample_and_both_repairs(self) -> None:
        text = SOURCE.read_text(encoding="utf-8")
        for declaration in (
            "removal_only_same_identity_rejoin_revives_capability",
            "coupled_removal_prevents_same_identity_capability_revival",
            "fresh_incarnation_does_not_inherit_old_capability",
        ):
            self.assertIn(declaration, text)

    def test_kernel_pending_boundary_cannot_be_misread_as_verified(self) -> None:
        text = README.read_text(encoding="utf-8").lower()
        self.assertIn("kernel-pending", text)
        self.assertNotIn("kernel-verified", text)


if __name__ == "__main__":
    unittest.main()
