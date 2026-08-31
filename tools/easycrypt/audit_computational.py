#!/usr/bin/env python3
"""Mechanical source audit for the computational EasyCrypt development.

The scanner lexes EasyCrypt comments and strings rather than relying only on
regular-expression grep.  The default checkpoint mode audits every source that
exists.  ``--release`` additionally requires the complete handoff layout and a
non-skeleton assumption manifest.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path
import re
import sys
from typing import Iterable

REQUIRED_LAYOUT = {
    "ProtocolTypes.ec",
    "CanonicalEncoding.ec",
    "AuthorizationState.ec",
    "ProtocolOracles.ec",
    "ImportedSecurity.eca",
    "BeeKemKiInterface.eca",
    "PrimitiveGames.eca",
    "UnauthorizedGame.ec",
    "UnauthorizedReduction.ec",
    "LiveKeyGame.ec",
    "LiveKeyReduction.ec",
    "ContentKeyGame.ec",
    "ContentKeyReduction.ec",
    "MutationWitnesses.ec",
    "Main.ec",
    "ASSUMPTION_MANIFEST.json",
    "README.md",
}

ALLOWED_AXIOM_FILES = {"ImportedSecurity.eca", "BeeKemKiInterface.eca"}
PLACEHOLDERS = {"admit", "abort", "sorry"}
FORBIDDEN_IDENTIFIERS = {"extra_checks", "ProtocolGate"}
FINAL_GAME_NAMES = {
    "ProtocolReal",
    "UnauthorizedReal",
    "LiveReal",
    "ContentReal",
    "AdvUnauthorized",
    "AdvLive",
    "AdvContent",
}
BEEKEM_THEOREM_AXIOM = "beekem_theorem1_imported_normalized"
BEEKEM_THEOREM_FILE = "BeeKemKiInterface.eca"


@dataclass(frozen=True)
class Finding:
    path: Path
    line: int
    message: str

    def render(self, root: Path) -> str:
        return f"{self.path.relative_to(root)}:{self.line}: {self.message}"


def strip_comments_and_strings(text: str) -> str:
    """Replace nested comments/string contents with spaces, preserving lines."""

    out: list[str] = []
    i = 0
    comment_depth = 0
    in_string = False
    escaped = False

    while i < len(text):
        pair = text[i : i + 2]
        char = text[i]

        if comment_depth:
            if pair == "(*":
                out.extend("  ")
                comment_depth += 1
                i += 2
                continue
            if pair == "*)":
                out.extend("  ")
                comment_depth -= 1
                i += 2
                continue
            out.append("\n" if char == "\n" else " ")
            i += 1
            continue

        if in_string:
            if char == "\n":
                out.append("\n")
                escaped = False
            else:
                out.append(" ")
                if escaped:
                    escaped = False
                elif char == "\\":
                    escaped = True
                elif char == '"':
                    in_string = False
            i += 1
            continue

        if pair == "(*":
            out.extend("  ")
            comment_depth = 1
            i += 2
            continue
        if char == '"':
            out.append(" ")
            in_string = True
            i += 1
            continue
        out.append(char)
        i += 1

    if comment_depth:
        raise ValueError("unterminated EasyCrypt comment")
    if in_string:
        raise ValueError("unterminated EasyCrypt string")
    return "".join(out)


def line_for_offset(text: str, offset: int) -> int:
    return text.count("\n", 0, offset) + 1


def declarations(clean: str, keyword: str) -> Iterable[tuple[str, int, str]]:
    pattern = re.compile(rf"\b{re.escape(keyword)}\s+([A-Za-z_][A-Za-z0-9_']*)")
    for match in pattern.finditer(clean):
        end = _declaration_end(clean, match.end())
        yield match.group(1), line_for_offset(clean, match.start()), clean[match.start() : end]


def _declaration_end(clean: str, start: int) -> int:
    depth = 0
    i = start
    while i < len(clean):
        char = clean[i]
        if char in "([{":
            depth += 1
        elif char in ")]}":
            depth = max(0, depth - 1)
        elif char == "." and depth == 0:
            return i + 1
        i += 1
    return len(clean)


def _require_pattern(
    findings: list[Finding],
    path: Path,
    line: int,
    text: str,
    pattern: str,
    message: str,
) -> None:
    if re.search(pattern, text, flags=re.DOTALL) is None:
        findings.append(Finding(path, line, message))


def audit_beekem_theorem_boundary(
    path: Path,
    clean: str,
    declaration: str,
    line: int,
) -> list[Finding]:
    """Reject theorem-boundary shapes that can make Theorem 1 vacuous/stronger.

    Appendix B states reductions produced for the challenged KI adversary and
    the concrete BeeKEM instance.  The source encodes that dependency with the
    quantifier order ``forall A, PaperInstance ... exists BNike, BSe``.  A
    section-level ``declare module BNike`` or ``declare module BSe`` would make
    those adversaries unrelated universal parameters and must never pass CI.
    """

    findings: list[Finding] = []

    required_file_patterns = (
        (
            r"\bdeclare\s+module\s+A\s*<:\s*BEEKEM_KI_ADVERSARY\s*\.",
            "BeeKEM theorem boundary must universally quantify the KI adversary A",
        ),
        (
            r"\bdeclare\s+module\s+PaperInstance\s*<:\s*BEEKEM_PAPER_INSTANCE\s*\.",
            "BeeKEM theorem boundary must universally quantify one paper instance",
        ),
        (
            r"\bmodule\s+PaperBeeKem\s*=\s*BeeKemProtocolOfPaperInstance\s*\(\s*PaperInstance\s*\)\s*\.",
            "BeeKEM protocol game must use the protocol adapter of PaperInstance",
        ),
        (
            r"\bmodule\s+Nike\s*=\s*BeeKemNikeOfPaperInstance\s*\(\s*PaperInstance\s*\)\s*\.",
            "HKR-CKS game must use the NIKE adapter of PaperInstance",
        ),
        (
            r"\bmodule\s+NikeKeySampler\s*=\s*BeeKemNikeSamplerOfPaperInstance\s*\(\s*PaperInstance\s*\)\s*\.",
            "HKR-CKS random branch must use the sampler of PaperInstance",
        ),
        (
            r"\bmodule\s+Se\s*=\s*BeeKemSeOfPaperInstance\s*\(\s*PaperInstance\s*\)\s*\.",
            "MU-CPA game must use the encryption adapter of PaperInstance",
        ),
        (
            r"\bmodule\s+PaperGame\s*=\s*BeeKemKiGame\s*\(\s*A\s*,\s*PaperBeeKem\s*\)\s*\.",
            "BeeKEM KI game must be instantiated by A and PaperInstance",
        ),
    )
    for pattern, message in required_file_patterns:
        _require_pattern(findings, path, line, clean, pattern, message)

    for reduction_name in ("BNike", "BSe"):
        match = re.search(
            rf"\bdeclare\s+module\s+{re.escape(reduction_name)}\b", clean
        )
        if match is not None:
            findings.append(
                Finding(
                    path,
                    line_for_offset(clean, match.start()),
                    f"{reduction_name} must be an existential Appendix-B witness, not a universal declared module",
                )
            )

    required_axiom_patterns = (
        (
            r"\b1\s*<=\s*kappa\b",
            "BeeKEM theorem axiom must require finite positive kappa",
        ),
        (
            r"\b0\s*<=\s*c\b",
            "BeeKEM theorem axiom must require a nonnegative challenge bound",
        ),
        (
            r"\bbeekem_is_ceil_log2\s+n\s+h\b",
            "BeeKEM theorem axiom must bind h to ceil(log2 n)",
        ),
        (
            r"\bNikeSymmetryGame\s*\.\s*main\s*\(\s*\)\s*@\s*&m\s*:\s*res\s*\]\s*=\s*1%r",
            "BeeKEM theorem axiom must require NIKE correctness/symmetry",
        ),
        (
            r"\bSeCorrectnessGame\s*\.\s*main\s*\(\s*message\s*\)\s*@\s*&m\s*:\s*res\s*\]\s*=\s*1%r",
            "BeeKEM theorem axiom must state the exact perfect-correctness specialization",
        ),
        (
            r"\bPaperGame\s*\.\s*main_with_evidence\s*\(",
            "BeeKEM theorem axiom must derive query bounds from executable game evidence",
        ),
        (
            r"res\s*\.\s*`bke_challenge_count\s*<=\s*c\b",
            "BeeKEM theorem axiom must bound executed challenge queries by c",
        ),
        (
            r"res\s*\.\s*`bke_member_addition_count\s*<=\s*n\b",
            "BeeKEM theorem axiom must bound executed member additions by n",
        ),
        (
            r"\bexists\s*\(\s*BNike\s*<:\s*BEEKEM_HKR_CKS_ADVERSARY\s*\)\s*,",
            "BeeKEM theorem axiom must existentially produce the HKR-CKS reduction",
        ),
        (
            r"\bexists\s*\(\s*BSe\s*<:\s*BEEKEM_MU_CPA_ADVERSARY\s*\)\s*,",
            "BeeKEM theorem axiom must existentially produce the MU-CPA reduction",
        ),
        (
            r"\bbeekem_normalized_ki_advantage\s*\(\s*Pr\s*\[\s*PaperGame\s*\.\s*main\s*\(",
            "BeeKEM theorem axiom must bound the named executable KI game",
        ),
        (
            r"\bbeekem_theorem1_loss\s+c\s+h\b",
            "BeeKEM theorem axiom must retain the c * ceil(log2 n) loss",
        ),
        (
            r"\bbeekem_hkr_cks_advantage\s*\(\s*Pr\s*\[\s*BeeKemHkrCksGame\s*\(\s*BNike\s*,",
            "BeeKEM theorem axiom must connect BNike to the named HKR-CKS game",
        ),
        (
            r"\bbeekem_mu_cpa_advantage\s*\(\s*Pr\s*\[\s*BeeKemMuCpaGame\s*\(\s*BSe\s*,",
            "BeeKEM theorem axiom must connect BSe to the named MU-CPA game",
        ),
    )
    for pattern, message in required_axiom_patterns:
        _require_pattern(findings, path, line, declaration, pattern, message)

    nike_position = declaration.find("exists (BNike")
    se_position = declaration.find("exists (BSe")
    bound_position = declaration.find("beekem_normalized_ki_advantage")
    if not (0 <= nike_position < se_position < bound_position):
        findings.append(
            Finding(
                path,
                line,
                "BeeKEM theorem axiom must quantify BNike then BSe before the reduction bound",
            )
        )

    return findings


def audit_source(path: Path, root: Path, manifest_names: set[str]) -> list[Finding]:
    findings: list[Finding] = []
    raw = path.read_text(encoding="utf-8")
    try:
        clean = strip_comments_and_strings(raw)
    except ValueError as error:
        return [Finding(path, 1, str(error))]

    for match in re.finditer(r"\b[A-Za-z_][A-Za-z0-9_']*\b", clean):
        token = match.group(0)
        line = line_for_offset(clean, match.start())
        if token.lower() in PLACEHOLDERS:
            findings.append(Finding(path, line, f"forbidden placeholder token: {token}"))
        if token in FORBIDDEN_IDENTIFIERS:
            findings.append(Finding(path, line, f"forbidden unconstrained gate: {token}"))
        if token == "negl":
            findings.append(Finding(path, line, "unexplained negl operator is forbidden"))

    target_axioms = 0
    for keyword in ("axiom",):
        for name, line, declaration in declarations(clean, keyword):
            if path.name not in ALLOWED_AXIOM_FILES:
                findings.append(Finding(path, line, "axiom outside imported-theory allowlist"))
            if name not in manifest_names:
                findings.append(Finding(path, line, f"axiom {name} absent from manifest"))
            if any(game_name in declaration for game_name in FINAL_GAME_NAMES):
                findings.append(
                    Finding(path, line, f"axiom {name} mentions a protocol final game/advantage")
                )
            if re.search(r"abs\s*\(\s*Pr\[", declaration):
                findings.append(
                    Finding(path, line, f"axiom {name} has adjacent-game conclusion shape")
                )
            if name == BEEKEM_THEOREM_AXIOM:
                target_axioms += 1
                if path.name != BEEKEM_THEOREM_FILE:
                    findings.append(
                        Finding(
                            path,
                            line,
                            f"{BEEKEM_THEOREM_AXIOM} must live only in {BEEKEM_THEOREM_FILE}",
                        )
                    )
                else:
                    findings.extend(
                        audit_beekem_theorem_boundary(path, clean, declaration, line)
                    )

    if path.name == BEEKEM_THEOREM_FILE and target_axioms != 1:
        findings.append(
            Finding(
                path,
                1,
                f"{BEEKEM_THEOREM_FILE} must contain exactly one {BEEKEM_THEOREM_AXIOM} axiom",
            )
        )

    for match in re.finditer(r"\baccept\s*\(\s*\)", clean):
        findings.append(
            Finding(path, line_for_offset(clean, match.start()), "parameterless accept() gate")
        )

    return findings


def load_manifest(path: Path) -> tuple[dict, set[str], list[Finding]]:
    if not path.exists():
        return {}, set(), [Finding(path, 1, "assumption manifest missing")]
    try:
        document = json.loads(path.read_text(encoding="utf-8"))
    except (json.JSONDecodeError, OSError) as error:
        return {}, set(), [Finding(path, 1, f"invalid assumption manifest: {error}")]
    declarations_value = document.get("declarations")
    if not isinstance(declarations_value, list):
        return document, set(), [Finding(path, 1, "manifest declarations must be a list")]
    names: set[str] = set()
    findings: list[Finding] = []
    for entry in declarations_value:
        if not isinstance(entry, dict) or not isinstance(entry.get("name"), str):
            findings.append(Finding(path, 1, "every manifest declaration needs a name"))
            continue
        name = entry["name"]
        if name in names:
            findings.append(Finding(path, 1, f"duplicate manifest declaration: {name}"))
        names.add(name)
    return document, names, findings


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("formal/current-source/easycrypt/computational"),
    )
    parser.add_argument("--release", action="store_true")
    args = parser.parse_args()
    root = args.root.resolve()

    findings: list[Finding] = []
    if not root.exists():
        print(f"missing computational directory: {root}", file=sys.stderr)
        return 1

    manifest_path = root / "ASSUMPTION_MANIFEST.json"
    manifest, manifest_names, manifest_findings = load_manifest(manifest_path)
    findings.extend(manifest_findings)

    source_files = sorted((*root.glob("*.ec"), *root.glob("*.eca")))
    for path in source_files:
        findings.extend(audit_source(path, root, manifest_names))

    declared_axioms: set[str] = set()
    for path in source_files:
        clean = strip_comments_and_strings(path.read_text(encoding="utf-8"))
        declared_axioms.update(name for name, _, _ in declarations(clean, "axiom"))
    for undeclared in sorted(manifest_names - declared_axioms):
        findings.append(Finding(manifest_path, 1, f"manifest axiom not found: {undeclared}"))

    if args.release:
        present = {path.name for path in root.iterdir() if path.is_file()}
        for missing in sorted(REQUIRED_LAYOUT - present):
            findings.append(Finding(root / missing, 1, "required release file missing"))
        if manifest.get("status") != "release":
            findings.append(Finding(manifest_path, 1, "release audit requires status=release"))

    if findings:
        for finding in findings:
            print(finding.render(root))
        return 1

    mode = "release" if args.release else "checkpoint"
    print(
        f"computational EasyCrypt {mode} audit passed: "
        f"{len(source_files)} EasyCrypt sources, {len(manifest_names)} manifest axioms"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
