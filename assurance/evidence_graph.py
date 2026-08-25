"""Strict proof-to-source-to-binary evidence graph validation.

The validator checks exact file hashes, anchored declaration patterns, a DAG of
explicit dependencies, binary metadata bindings, target-bound measurements,
and load-bearing negative controls. It deliberately rejects documentation or
the evidence graph itself as sufficient proof of a verified claim.
"""

from __future__ import annotations

import hashlib
import json
import re
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping

from .target_evidence import validate_target_bound_measurement

ALLOWED_KINDS = {
    "source",
    "proof",
    "binary",
    "measurement",
    "negative_control",
    "documentation",
    "derivation",
}


@dataclass(frozen=True)
class EvidenceGraphValidation:
    valid: bool
    errors: tuple[str, ...]
    actual_hashes: dict[str, str]


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _hex(value: object, length: int) -> bool:
    return (
        isinstance(value, str)
        and len(value) == length
        and all(character in "0123456789abcdef" for character in value)
    )


def _resolve(root: Path, relative: object, errors: list[str], label: str) -> Path | None:
    if not isinstance(relative, str) or not relative:
        errors.append(f"{label} has no relative path")
        return None
    path = (root / relative).resolve()
    try:
        path.relative_to(root.resolve())
    except ValueError:
        errors.append(f"{label} path escapes the repository: {relative}")
        return None
    return path


def _cycle_errors(nodes: Mapping[str, Mapping[str, Any]]) -> list[str]:
    errors: list[str] = []
    visiting: set[str] = set()
    visited: set[str] = set()

    def visit(node_id: str, trail: tuple[str, ...]) -> None:
        if node_id in visited:
            return
        if node_id in visiting:
            start = trail.index(node_id) if node_id in trail else 0
            cycle = (*trail[start:], node_id)
            errors.append("evidence dependency cycle: " + " -> ".join(cycle))
            return
        visiting.add(node_id)
        node = nodes[node_id]
        dependencies = node.get("depends_on", [])
        if isinstance(dependencies, list):
            for dependency in dependencies:
                if isinstance(dependency, str) and dependency in nodes:
                    visit(dependency, (*trail, node_id))
        visiting.remove(node_id)
        visited.add(node_id)

    for node_id in nodes:
        visit(node_id, ())
    return errors


def validate_evidence_graph(
    document: Mapping[str, Any],
    *,
    root: Path,
    graph_path: Path | None = None,
) -> EvidenceGraphValidation:
    errors: list[str] = []
    hashes: dict[str, str] = {}
    if document.get("schema") != "causal-dag-assurance.evidence-graph.v2":
        errors.append("unexpected evidence graph schema")

    raw_nodes = document.get("nodes")
    if not isinstance(raw_nodes, list) or not raw_nodes:
        errors.append("nodes must be a non-empty list")
        raw_nodes = []

    nodes: dict[str, Mapping[str, Any]] = {}
    paths: dict[str, Path] = {}
    for raw in raw_nodes:
        if not isinstance(raw, Mapping):
            errors.append("evidence node must be an object")
            continue
        node_id = raw.get("id")
        if not isinstance(node_id, str) or not node_id:
            errors.append("evidence node has no id")
            continue
        if node_id in nodes:
            errors.append(f"duplicate evidence node id: {node_id}")
            continue
        nodes[node_id] = raw
        kind = raw.get("kind")
        if kind not in ALLOWED_KINDS:
            errors.append(f"{node_id}: unsupported evidence kind {kind!r}")

        path = _resolve(root, raw.get("path"), errors, node_id)
        if path is None:
            continue
        paths[node_id] = path
        if graph_path is not None and path == graph_path.resolve():
            errors.append(f"{node_id}: evidence graph cannot attest to itself")
        if not path.is_file():
            errors.append(f"{node_id}: missing evidence file {raw.get('path')}")
            continue
        actual = _sha256(path)
        hashes[node_id] = actual
        expected = raw.get("sha256")
        if not _hex(expected, 64):
            errors.append(f"{node_id}: invalid expected SHA-256")
        elif expected != actual:
            errors.append(f"{node_id}: stale or incorrect file SHA-256")

        if kind in {"source", "proof"}:
            declarations = raw.get("declarations")
            if not isinstance(declarations, list) or not declarations:
                errors.append(f"{node_id}: source/proof node has no declarations")
            else:
                text = path.read_text(encoding="utf-8", errors="replace")
                for declaration in declarations:
                    if not isinstance(declaration, Mapping):
                        errors.append(f"{node_id}: declaration must be an object")
                        continue
                    pattern = declaration.get("pattern")
                    expected_count = declaration.get("count", 1)
                    if (
                        not isinstance(pattern, str)
                        or not pattern.startswith("^")
                        or not pattern.endswith("$")
                    ):
                        errors.append(
                            f"{node_id}: declaration pattern must be line-anchored"
                        )
                        continue
                    try:
                        observed = len(re.findall(pattern, text, flags=re.MULTILINE))
                    except re.error as error:
                        errors.append(f"{node_id}: invalid declaration regex: {error}")
                        continue
                    if observed != expected_count:
                        errors.append(
                            f"{node_id}: declaration count {observed} != {expected_count}"
                        )

    for node_id, node in nodes.items():
        dependencies = node.get("depends_on", [])
        if not isinstance(dependencies, list) or not all(
            isinstance(item, str) for item in dependencies
        ):
            errors.append(f"{node_id}: depends_on must be a string list")
            continue
        for dependency in dependencies:
            if dependency not in nodes:
                errors.append(f"{node_id}: missing dependency {dependency}")
            if dependency == node_id:
                errors.append(f"{node_id}: self dependency is forbidden")

    errors.extend(_cycle_errors(nodes))

    for node_id, node in nodes.items():
        kind = node.get("kind")
        if kind == "binary":
            metadata_path = _resolve(
                root, node.get("metadata_path"), errors, f"{node_id}.metadata"
            )
            if metadata_path is None or not metadata_path.is_file():
                errors.append(f"{node_id}: missing binary metadata file")
                continue
            metadata_hash = _sha256(metadata_path)
            if metadata_hash != node.get("metadata_sha256"):
                errors.append(f"{node_id}: binary metadata SHA-256 mismatch")
            try:
                metadata = json.loads(metadata_path.read_text(encoding="utf-8"))
            except (OSError, json.JSONDecodeError) as error:
                errors.append(f"{node_id}: invalid binary metadata: {error}")
                continue
            for field, length in (
                ("source_commit", 40),
                ("source_tree_sha256", 64),
            ):
                if not _hex(node.get(field), length):
                    errors.append(f"{node_id}: invalid {field}")
                if metadata.get(field) != node.get(field):
                    errors.append(f"{node_id}: metadata {field} mismatch")
            if metadata.get("binary_sha256") != hashes.get(node_id):
                errors.append(f"{node_id}: metadata binary_sha256 mismatch")

        if kind == "measurement":
            binary_id = node.get("binary_node")
            binary = nodes.get(binary_id) if isinstance(binary_id, str) else None
            if not isinstance(binary, Mapping) or binary.get("kind") != "binary":
                errors.append(f"{node_id}: binary_node does not name a binary node")
                continue
            binary_manifest = {
                "binary_sha256": hashes.get(str(binary_id)),
                "source_commit": binary.get("source_commit"),
                "source_tree_sha256": binary.get("source_tree_sha256"),
                "target": binary.get("target"),
            }
            measurement_record = dict(node)
            measurement_record["artifact_path"] = node.get("path")
            measurement_record["artifact_sha256"] = node.get("sha256")
            result = validate_target_bound_measurement(
                measurement_record, binary_manifest, root=root
            )
            errors.extend(f"{node_id}: {error}" for error in result.errors)

        if kind == "negative_control":
            path = paths.get(node_id)
            if path is None or not path.is_file():
                continue
            try:
                outcome = json.loads(path.read_text(encoding="utf-8"))
            except json.JSONDecodeError:
                errors.append(f"{node_id}: negative-control result is not JSON")
                continue
            if outcome.get("expected_failure_observed") is not True:
                errors.append(f"{node_id}: expected failure was not observed")
            if not isinstance(outcome.get("failure_reason"), str) or not outcome.get(
                "failure_reason"
            ):
                errors.append(f"{node_id}: negative control has no failure reason")

    claims = document.get("claims")
    if not isinstance(claims, list):
        errors.append("claims must be a list")
        claims = []
    claim_ids: set[str] = set()
    for claim in claims:
        if not isinstance(claim, Mapping):
            errors.append("claim must be an object")
            continue
        claim_id = claim.get("id")
        if not isinstance(claim_id, str) or not claim_id:
            errors.append("claim has no id")
            continue
        if claim_id in claim_ids:
            errors.append(f"duplicate claim id: {claim_id}")
        claim_ids.add(claim_id)
        status = claim.get("status")
        if status not in {"open", "verified"}:
            errors.append(f"{claim_id}: invalid status {status!r}")
        evidence = claim.get("evidence")
        if not isinstance(evidence, list) or not all(
            isinstance(item, str) for item in evidence
        ):
            errors.append(f"{claim_id}: evidence must be a string list")
            continue
        missing = [item for item in evidence if item not in nodes]
        if missing:
            errors.append(f"{claim_id}: unknown evidence nodes {missing}")
        if status == "verified":
            kinds = {
                nodes[item].get("kind") for item in evidence if item in nodes
            }
            if not kinds - {"documentation"}:
                errors.append(
                    f"{claim_id}: documentation cannot be the sole verification evidence"
                )
            if "negative_control" not in kinds:
                errors.append(
                    f"{claim_id}: verified claim has no load-bearing negative control"
                )

    return EvidenceGraphValidation(
        valid=not errors, errors=tuple(errors), actual_hashes=hashes
    )
