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

        imports = re.findall(r"^import\s+CausalDagCgka\.(.+)$", main, re.MULTILINE)
        missing = [
            module
            for module in imports
            if not (MAIN.parent / f"{module}.lean").is_file()
        ]
        self.assertEqual(missing, [])

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

    def test_wasm_green_boundary_cannot_be_misread_as_exact_pin(self) -> None:
        text = README.read_text(encoding="utf-8").lower()
        self.assertIn("80-theorem source closure passes", text)
        self.assertIn("lean wasm", text)
        self.assertIn("exact pinned lean 4.32.2", text)
        self.assertIn("remains pending", text)
        self.assertRegex(
            text,
            r"must not\s+be described as an exact-toolchain package build",
        )


if __name__ == "__main__":
    unittest.main()
