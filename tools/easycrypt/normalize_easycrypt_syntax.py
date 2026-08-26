#!/usr/bin/env python3
"""Deterministically normalize the computational EasyCrypt source syntax.

This is a narrow migration helper for the Milestone 1 branch. It is idempotent:
record projections are derived from declared record types, concrete files stop
importing the abstract primitive-game theory, and invalid `return <@` calls in
the mutation harness are rewritten through an explicit local result variable.
"""

from __future__ import annotations

from pathlib import Path
import re

ROOT = Path("formal/current-source/easycrypt/computational")
SOURCE_FILES = sorted([*ROOT.glob("*.ec"), *ROOT.glob("*.eca")])


def declared_record_fields() -> set[str]:
    fields: set[str] = set()
    for path in SOURCE_FILES:
        in_record = False
        for line in path.read_text(encoding="utf-8").splitlines():
            if re.match(r"^\s*type\s+[A-Za-z_][A-Za-z0-9_]*\s*=\s*\{\s*$", line):
                in_record = True
                continue
            if in_record and re.match(r"^\s*\}\.?\s*$", line):
                in_record = False
                continue
            if in_record:
                match = re.match(r"^\s*([a-z][A-Za-z0-9_]*)\s*:", line)
                if match:
                    fields.add(match.group(1))
    return fields


def normalize_record_projections(fields: set[str]) -> None:
    for path in SOURCE_FILES:
        text = path.read_text(encoding="utf-8")
        normalized = text
        for field in sorted(fields, key=len, reverse=True):
            normalized = re.sub(
                r"\." + re.escape(field) + r"\b",
                ".`" + field,
                normalized,
            )
        if path.suffix == ".ec":
            normalized = normalized.replace(
                "require import ProtocolTypes CanonicalEncoding PrimitiveGames AuthorizationState.",
                "require import ProtocolTypes CanonicalEncoding ProtocolPrimitives AuthorizationState.",
            )
        if normalized != text:
            path.write_text(normalized, encoding="utf-8")


def procedure_end(lines: list[str], start: int) -> int:
    depth = 1
    index = start + 1
    while index < len(lines):
        # Record literals use {| and |}; raw braces here delimit procedures.
        depth += lines[index].count("{") - lines[index].count("}")
        if depth == 0:
            return index
        index += 1
    raise RuntimeError(f"unterminated procedure beginning at line {start + 1}")


def normalize_mutation_returns() -> None:
    path = ROOT / "MutationWitnesses.ec"
    lines = path.read_text(encoding="utf-8").splitlines()

    return_indexes = [index for index, line in enumerate(lines) if "return <@" in line]
    if not return_indexes:
        return

    procedures: list[tuple[int, int]] = []
    for index, line in enumerate(lines):
        if re.search(r"proc\s+main\(\)\s*:\s*bool\s*\*\s*int\s*=\s*\{", line):
            procedures.append((index, procedure_end(lines, index)))

    for start, end in reversed(procedures):
        if not any(start < index < end for index in return_indexes):
            continue
        insert_at = start + 1
        while insert_at < end and (
            lines[insert_at].lstrip().startswith("var ")
            or lines[insert_at].strip() == ""
        ):
            insert_at += 1
        if not any("var outcome : bool * int;" in line for line in lines[start:end]):
            lines.insert(insert_at, "    var outcome : bool * int;")

    index = 0
    while index < len(lines):
        if "return <@" not in lines[index]:
            index += 1
            continue
        lines[index] = lines[index].replace("return <@", "outcome <@")
        terminator = index + 1
        while terminator < len(lines) and lines[terminator].strip() != ");":
            terminator += 1
        if terminator == len(lines):
            raise RuntimeError(f"no call terminator after line {index + 1}")
        lines.insert(terminator + 1, "    return outcome;")
        index = terminator + 2

    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    fields = declared_record_fields()
    normalize_record_projections(fields)
    normalize_mutation_returns()

    remaining_returns = []
    remaining_plain_projections = []
    projection_pattern = re.compile(
        r"\.(?:p_|oe_|ot_|sig_|af_|saf_|pv_|nm_|mge_|cge_|as_|snapshot_|"
        r"ri_|sce_|he_|ps_|ao_|vr_|wf_)[A-Za-z0-9_]+"
    )
    for path in SOURCE_FILES:
        for line_number, line in enumerate(
            path.read_text(encoding="utf-8").splitlines(), start=1
        ):
            if "return <@" in line:
                remaining_returns.append(f"{path}:{line_number}:{line}")
            if projection_pattern.search(line):
                remaining_plain_projections.append(
                    f"{path}:{line_number}:{line}"
                )

    if remaining_returns or remaining_plain_projections:
        raise SystemExit(
            "normalization incomplete:\n"
            + "\n".join(remaining_returns + remaining_plain_projections)
        )

    print(f"normalized {len(SOURCE_FILES)} EasyCrypt files using {len(fields)} fields")


if __name__ == "__main__":
    main()
