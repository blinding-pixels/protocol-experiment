#!/usr/bin/env python3
"""Run all local assumption-reduction checks and emit a hashable report."""

from __future__ import annotations

import argparse
import hashlib
import json
import platform
import sys
import unittest
from pathlib import Path


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


class RecordingResult(unittest.TextTestResult):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.successes: list[str] = []

    def addSuccess(self, test):  # noqa: N802
        self.successes.append(test.id())
        super().addSuccess(test)


def suite(root: Path) -> unittest.TestSuite:
    loader = unittest.TestLoader()
    combined = unittest.TestSuite()
    combined.addTests(loader.discover(str(root / "attack_lab/tests"), top_level_dir=str(root)))
    combined.addTests(loader.discover(str(root / "assurance/tests"), top_level_dir=str(root)))
    combined.addTests(loader.discover(str(root / "formal/tests"), top_level_dir=str(root)))
    return combined


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    runner = unittest.TextTestRunner(verbosity=2, resultclass=RecordingResult)
    result = runner.run(suite(root))
    source_paths = sorted(
        [
            *root.glob("attack_lab/*.py"),
            *root.glob("attack_lab/tests/*.py"),
            *root.glob("assurance/*.py"),
            *root.glob("assurance/tests/*.py"),
            *root.glob("formal/*.py"),
            *root.glob("formal/tests/*.py"),
        ]
    )
    report = {
        "schema": "causal-dag-assurance.local-test-report.v1",
        "strict_pass": result.wasSuccessful(),
        "python": platform.python_version(),
        "tests_run": result.testsRun,
        "successes": sorted(result.successes),
        "failures": [test.id() for test, _ in result.failures],
        "errors": [test.id() for test, _ in result.errors],
        "skipped": [test.id() for test, _ in result.skipped],
        "negative_controls": sorted(
            test_id
            for test_id in result.successes
            if any(
                marker in test_id
                for marker in (
                    "mismatch",
                    "rejected",
                    "drift",
                    "forbidden",
                    "requires",
                    "cannot",
                    "missing",
                    "cycle",
                    "replacement",
                    "identical_binary",
                    "invalid_digest",
                    "duplicates",
                    "domain_change",
                    "version_change",
                    "component_position",
                    "counterexample",
                    "revival",
                    "rejoin",
                    "unqualified",
                    "kernel_pending",
                    "placeholder",
                    "unknown_assumption",
                )
            )
        ),
        "source_sha256": {
            str(path.relative_to(root)): sha256(path) for path in source_paths
        },
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(args.output)
    return 0 if result.wasSuccessful() else 1


if __name__ == "__main__":
    raise SystemExit(main())
