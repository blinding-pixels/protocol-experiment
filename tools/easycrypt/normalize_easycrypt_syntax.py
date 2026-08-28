#!/usr/bin/env python3
"""Deterministically normalize the computational EasyCrypt source syntax.

This is a narrow migration helper for the Milestone 1 branch. It is idempotent:
record projections are derived from declared record types, concrete files stop
importing the abstract primitive-game theory, grouped local declarations are
split, fixture operators use curried application, and invalid `return <@` calls
in the mutation harness are rewritten through an explicit local result variable.
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


def normalize_grouped_variables() -> None:
    declaration = re.compile(
        r"^(?P<indent>\s*)var\s+"
        r"(?P<names>[A-Za-z_][A-Za-z0-9_]*(?:\s+[A-Za-z_][A-Za-z0-9_]*)+)"
        r"\s*:\s*(?P<type>.+);\s*$"
    )
    for path in SOURCE_FILES:
        lines = path.read_text(encoding="utf-8").splitlines()
        normalized: list[str] = []
        changed = False
        for line in lines:
            match = declaration.match(line)
            if match is None:
                normalized.append(line)
                continue
            changed = True
            indent = match.group("indent")
            type_name = match.group("type")
            for name in match.group("names").split():
                normalized.append(f"{indent}var {name} : {type_name};")
        if changed:
            path.write_text("\n".join(normalized) + "\n", encoding="utf-8")


def matching_parenthesis(text: str, opening: int) -> int:
    depth = 0
    for index in range(opening, len(text)):
        if text[index] == "(":
            depth += 1
        elif text[index] == ")":
            depth -= 1
            if depth == 0:
                return index
    raise RuntimeError(f"unclosed parenthesis at byte {opening}")


def split_top_level_arguments(text: str) -> list[str]:
    arguments: list[str] = []
    start = 0
    depth = 0
    for index, character in enumerate(text):
        if character in "([{":
            depth += 1
        elif character in ")]}":
            depth -= 1
        elif character == "," and depth == 0:
            arguments.append(text[start:index].strip())
            start = index + 1
    arguments.append(text[start:].strip())
    return arguments


def normalize_curried_fixture_operators() -> None:
    path = ROOT / "MutationWitnesses.ec"
    text = path.read_text(encoding="utf-8")
    targets = {
        "witness_edit_envelope": 10,
        "witness_history_envelope": 7,
        "witness_public_view": 2,
    }

    for name, arity in targets.items():
        position = 0
        pattern = re.compile(r"\b" + re.escape(name) + r"\s*\(")
        while True:
            match = pattern.search(text, position)
            if match is None:
                break
            call_start = match.start()
            opening = text.find("(", call_start)
            closing = matching_parenthesis(text, opening)
            arguments = split_top_level_arguments(text[opening + 1 : closing])
            if len(arguments) != arity:
                position = closing + 1
                continue

            line_start = text.rfind("\n", 0, call_start) + 1
            prefix = text[line_start:call_start]
            indent_match = re.match(r"\s*", prefix)
            indent = indent_match.group(0) if indent_match is not None else ""
            continuation = indent + "  "

            if "\n" not in text[opening + 1 : closing] and sum(
                len(argument) for argument in arguments
            ) < 72:
                replacement = name + " " + " ".join(
                    f"({argument})" for argument in arguments
                )
            else:
                replacement = name + "\n" + "\n".join(
                    continuation + f"({argument})" for argument in arguments
                )

            text = text[:call_start] + replacement + text[closing + 1 :]
            position = call_start + len(replacement)

    path.write_text(text, encoding="utf-8")


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


def tuple_style_fixture_calls() -> list[str]:
    path = ROOT / "MutationWitnesses.ec"
    text = path.read_text(encoding="utf-8")
    leftovers: list[str] = []
    for name, arity in {
        "witness_edit_envelope": 10,
        "witness_history_envelope": 7,
        "witness_public_view": 2,
    }.items():
        pattern = re.compile(r"\b" + re.escape(name) + r"\s*\(")
        for match in pattern.finditer(text):
            opening = text.find("(", match.start())
            closing = matching_parenthesis(text, opening)
            arguments = split_top_level_arguments(text[opening + 1 : closing])
            if len(arguments) == arity:
                line = text.count("\n", 0, match.start()) + 1
                leftovers.append(f"{path}:{line}:{name}")
    return leftovers


def main() -> None:
    fields = declared_record_fields()
    normalize_record_projections(fields)
    normalize_grouped_variables()
    normalize_curried_fixture_operators()
    normalize_mutation_returns()

    remaining_returns: list[str] = []
    remaining_plain_projections: list[str] = []
    remaining_grouped_variables: list[str] = []
    projection_pattern = re.compile(
        r"\.(?:p_|oe_|ot_|sig_|af_|saf_|pv_|nm_|mge_|cge_|as_|snapshot_|"
        r"ri_|sce_|he_|ps_|ao_|vr_|wf_)[A-Za-z0-9_]+"
    )
    grouped_pattern = re.compile(
        r"^\s*var\s+[A-Za-z_][A-Za-z0-9_]*"
        r"(?:\s+[A-Za-z_][A-Za-z0-9_]*)+\s*:"
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
            if grouped_pattern.search(line):
                remaining_grouped_variables.append(
                    f"{path}:{line_number}:{line}"
                )

    leftovers = (
        remaining_returns
        + remaining_plain_projections
        + remaining_grouped_variables
        + tuple_style_fixture_calls()
    )
    if leftovers:
        raise SystemExit("normalization incomplete:\n" + "\n".join(leftovers))

    print(f"normalized {len(SOURCE_FILES)} EasyCrypt files using {len(fields)} fields")


if __name__ == "__main__":
    main()
