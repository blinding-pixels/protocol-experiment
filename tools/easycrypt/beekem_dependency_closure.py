#!/usr/bin/env python3
"""Compute the transitive local EasyCrypt dependency closure of one entry point.

Only local ``.ec``/``.eca`` theories under ``--root`` are emitted. System
libraries are intentionally ignored. A dependency whose name starts with a
configured local prefix but has no local source file is an error, so deleting a
required local source cannot silently shrink the recorded closure.
"""

from __future__ import annotations

import argparse
from collections import deque
from pathlib import Path
import re
import sys

IDENTIFIER = re.compile(r"[A-Za-z_][A-Za-z0-9_']*")
REQUIRE = re.compile(
    r"\brequire\s+(?:(?:import|export)\s+)?(?P<body>[^.]+)\.",
    re.MULTILINE,
)


def strip_comments_and_strings(text: str) -> str:
    """Replace nested comments and string contents while preserving newlines."""

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


def local_sources(root: Path) -> dict[str, Path]:
    sources: dict[str, Path] = {}
    for path in sorted((*root.glob("*.ec"), *root.glob("*.eca"))):
        previous = sources.get(path.stem)
        if previous is not None:
            raise ValueError(
                f"ambiguous local theory {path.stem}: {previous.name}, {path.name}"
            )
        sources[path.stem] = path
    return sources


def required_theories(path: Path) -> list[str]:
    clean = strip_comments_and_strings(path.read_text(encoding="utf-8"))
    names: list[str] = []
    for match in REQUIRE.finditer(clean):
        names.extend(IDENTIFIER.findall(match.group("body")))
    return names


def validate_entry(root: Path, entry: Path) -> dict[str, Path]:
    sources = local_sources(root)
    if entry.parent != root:
        raise ValueError("entry must be a direct child of --root")
    if not entry.is_file():
        raise ValueError(f"entry does not exist: {entry}")
    return sources


def resolve_dependency(
    current: Path,
    name: str,
    sources: dict[str, Path],
    local_prefixes: tuple[str, ...],
) -> Path | None:
    dependency = sources.get(name)
    if dependency is not None:
        return dependency
    if any(name.startswith(prefix) for prefix in local_prefixes):
        raise ValueError(
            f"{current.name}: unresolved required local theory {name}"
        )
    return None


def closure(
    root: Path,
    entry: Path,
    local_prefixes: tuple[str, ...],
) -> list[Path]:
    """Return the local closure in stable filename order."""

    sources = validate_entry(root, entry)
    seen: set[Path] = set()
    pending: deque[Path] = deque([entry])
    while pending:
        current = pending.popleft()
        if current in seen:
            continue
        seen.add(current)
        for name in required_theories(current):
            dependency = resolve_dependency(
                current, name, sources, local_prefixes
            )
            if dependency is not None and dependency not in seen:
                pending.append(dependency)

    return sorted(seen, key=lambda path: path.name)


def dependency_first_closure(
    root: Path,
    entry: Path,
    local_prefixes: tuple[str, ...],
) -> list[Path]:
    """Return each dependency before the theory that requires it."""

    sources = validate_entry(root, entry)
    states: dict[Path, int] = {}
    stack: list[Path] = []
    ordered: list[Path] = []

    def visit(current: Path) -> None:
        state = states.get(current, 0)
        if state == 2:
            return
        if state == 1:
            cycle_start = stack.index(current)
            cycle = stack[cycle_start:] + [current]
            raise ValueError(
                "local dependency cycle: "
                + " -> ".join(path.name for path in cycle)
            )

        states[current] = 1
        stack.append(current)
        for name in required_theories(current):
            dependency = resolve_dependency(
                current, name, sources, local_prefixes
            )
            if dependency is not None:
                visit(dependency)
        stack.pop()
        states[current] = 2
        ordered.append(current)

    visit(entry)
    return ordered


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("formal/current-source/easycrypt/computational"),
    )
    parser.add_argument("--entry", default="BeeKemInterfaceProof.ec")
    parser.add_argument(
        "--local-prefix",
        action="append",
        default=["BeeKem"],
        help="missing dependencies with this prefix are errors; repeatable",
    )
    parser.add_argument(
        "--repository-relative",
        action="store_true",
        help="emit paths relative to the current working directory",
    )
    parser.add_argument(
        "--dependency-first",
        action="store_true",
        help="emit a deterministic topological order suitable for direct checks",
    )
    args = parser.parse_args()

    root = args.root.resolve()
    entry = (root / args.entry).resolve()
    try:
        if args.dependency_first:
            result = dependency_first_closure(
                root, entry, tuple(args.local_prefix)
            )
        else:
            result = closure(root, entry, tuple(args.local_prefix))
    except (OSError, UnicodeError, ValueError) as error:
        print(f"dependency-closure error: {error}", file=sys.stderr)
        return 1

    cwd = Path.cwd().resolve()
    for path in result:
        if args.repository_relative:
            try:
                print(path.relative_to(cwd))
            except ValueError:
                print(path)
        else:
            print(path.relative_to(root))
    print(
        f"dependency-closure count: {len(result)}",
        file=sys.stderr,
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
