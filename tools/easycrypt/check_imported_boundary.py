#!/usr/bin/env python3
"""Fail closed if the existing imported BeeKEM boundary proves a contradiction.

The counterexample's whole local dependency closure is compiled first, without
importing the security axiom. The contradiction theory is quarantined outside
the production proof directory. An accepted contradiction is FAILURE, never a
successful proof milestone. Rejection of this reproducer is not a consistency
proof; all other acceptance requirements remain necessary.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import signal
import subprocess
import sys
import tempfile
import time

IMAGE = "ghcr.io/easycrypt/ec-test-box@sha256:84980006e8b01fe6497bbd0ecd67deeb5e7361d8ad17e27d24924122d368e0fc"
POSITIVE = "BeeKemBoundaryCounterexample.ec"
SANITY = "BeeKemBoundaryNoAxiomSanity.ec"
CONTRADICTION = "BeeKemBoundaryContradiction.ec"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def semantic_rejection(record: dict, log: str, target: str) -> bool:
    if record["exit_status"] != 1 or record["timed_out"] or record["eco_nonempty"]:
        return False
    critical = log[log.rfind("[critical]"):]
    if "[critical]" not in critical or target not in critical:
        return False
    if any(s in critical.lower() for s in (
        "parse error", "unknown", "no such object", "cannot import", "invalid name",
    )):
        return False
    return (
        "cannot prove goal (strict)" in critical
        or "the given proof-term proves:" in critical
        or "this proof-term proves" in critical
        or ("module" in critical.lower() and any(s in critical.lower() for s in (
            "can read", "can write", "does not satisfy the restriction", "not allowed to use",
        )))
    )


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repository", type=Path, default=Path(__file__).resolve().parents[2])
    ap.add_argument("--evidence", type=Path, required=True)
    ap.add_argument("--timeout", type=int, default=180)
    ap.add_argument("--chroot", type=Path, help="Use an already verified exported pinned rootfs instead of Docker.")
    args = ap.parse_args()
    if args.timeout <= 0:
        ap.error("--timeout must be positive")
    repo = args.repository.resolve()
    evidence = args.evidence.resolve()
    evidence.mkdir(parents=True, exist_ok=True)
    if (evidence / "result.json").exists():
        ap.error("Use a new evidence directory; existing results are not overwritten")
    source = repo / "formal/current-source/easycrypt/computational"
    diagnostics = repo / "formal/current-source/easycrypt/diagnostics"
    helper = repo / "tools/easycrypt/beekem_dependency_closure.py"
    rootfs = args.chroot.resolve() if args.chroot else None
    result: dict = {"image": IMAGE, "runtime": "exported-rootfs" if rootfs else "docker", "checks": []}
    result["driver_sha256"] = sha256(Path(__file__).resolve())
    result["dependency_helper_sha256"] = sha256(helper)
    result["source_commit"] = subprocess.check_output(["git", "-C", str(repo), "rev-parse", "HEAD"], text=True).strip()
    result["git_status"] = subprocess.check_output(["git", "-C", str(repo), "status", "--porcelain"], text=True)

    def finish(status: str, code: int, message: str) -> int:
        result.update(status=status, guard_exit_status=code, message=message)
        (evidence / "result.json").write_text(json.dumps(result, indent=2) + "\n")
        print(json.dumps({"status": status, "guard_exit_status": code, "message": message}, indent=2), flush=True)
        return code

    # Only this new temporary directory becomes writable by the image's user.
    with tempfile.TemporaryDirectory(prefix="boundary-check-", dir=rootfs) as temp:
        work = Path(temp)
        work.chmod(0o777)
        for path in source.iterdir():
            if path.is_file() and path.suffix in (".ec", ".eca"):
                shutil.copyfile(path, work / path.name)
        for name in (POSITIVE, SANITY, CONTRADICTION):
            shutil.copyfile(diagnostics / name, work / name)
        def closure(entry: str) -> list[str]:
            return subprocess.check_output([
                sys.executable, str(helper), "--root", str(work), "--entry", entry,
                "--dependency-first", "--local-prefix", "BeeKem",
            ], text=True).splitlines()
        foundation = closure(POSITIVE)
        imported = closure(CONTRADICTION)
        if len(foundation) != len(set(foundation)) or len(imported) != len(set(imported)):
            return finish("INFRASTRUCTURE_FAILURE", 2, "Repeated dependency targets")
        if "BeeKemKiInterface.eca" in foundation or CONTRADICTION in foundation:
            return finish("QUARANTINE_FAILURE", 2, "The positive counterexample imports the disputed boundary")
        if set(imported) - set(foundation) != {"BeeKemKiInterface.eca", CONTRADICTION}:
            return finish("QUARANTINE_FAILURE", 2, "Unexpected extra dependency in contradiction theory")
        needed = set(imported) | {SANITY}
        for path in work.iterdir():
            if path.name not in needed:
                path.unlink()
        result["foundation_order"] = foundation
        result["contradiction_order"] = imported
        result["source_sha256"] = {name: sha256(work / name) for name in sorted(needed)}
        # Inspect declarations, not comments, using the repository's closure lexer.
        sys.path.insert(0, str(helper.parent))
        from beekem_dependency_closure import strip_comments_and_strings
        local_axioms = []
        for name in sorted(needed):
            clean = strip_comments_and_strings((work / name).read_text())
            local_axioms.extend((name, m.group(1)) for m in re.finditer(r"\baxiom\s+([A-Za-z_][A-Za-z0-9_']*)", clean))
        result["local_axiom_declarations"] = local_axioms
        if local_axioms != [("BeeKemKiInterface.eca", "beekem_theorem1_imported_normalized")]:
            return finish("QUARANTINE_FAILURE", 2, "Unexpected local axiom declaration set")
        copies = evidence / "source"
        copies.mkdir(exist_ok=True)
        for name in sorted(needed):
            shutil.copyfile(work / name, copies / name)

        def compile_target(target: str) -> tuple[dict, str]:
            eco = work / (Path(target).stem + ".eco")
            eco.unlink(missing_ok=True)
            expression = "exec timeout --kill-after=10s " + str(args.timeout) + "s opam exec -- easycrypt compile " + shlex.quote(target)
            if rootfs:
                inner = "/" + work.relative_to(rootfs).as_posix()
                command = ["chroot", "--userspec=1001:0", str(rootfs), "/usr/bin/env",
                           "HOME=/home/charlie", "PATH=/home/charlie/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
                           "/bin/bash", "-c", "cd " + shlex.quote(inner) + " && " + expression]
            else:
                command = ["docker", "run", "--rm", "--network", "none", "-v", str(work) + ":/proof",
                           "-w", "/proof", IMAGE, "bash", "-c", expression]
            stem = Path(target).stem
            stdout = evidence / (stem + "-stdout.log")
            stderr = evidence / (stem + "-stderr.log")
            started = time.monotonic()
            host_timeout = False
            with stdout.open("wb") as out, stderr.open("wb") as err:
                proc = subprocess.Popen(command, stdout=out, stderr=err, start_new_session=True)
                try:
                    code = proc.wait(timeout=args.timeout + 30)
                except subprocess.TimeoutExpired:
                    host_timeout = True
                    os.killpg(proc.pid, signal.SIGTERM)
                    try:
                        code = proc.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        os.killpg(proc.pid, signal.SIGKILL)
                        code = proc.wait()
            record = {
                "target": target, "command": command, "exit_status": code,
                "timed_out": host_timeout or code in (124, 137),
                "elapsed_seconds": time.monotonic() - started,
                "eco_nonempty": eco.exists() and eco.stat().st_size > 0,
                "eco_sha256": sha256(eco) if eco.exists() else None,
                "source_sha256": sha256(work / target),
            }
            result["checks"].append(record)
            (evidence / (stem + "-result.json")).write_text(json.dumps(record, indent=2) + "\n")
            print(target, "exit=" + str(code), "eco=" + str(record["eco_nonempty"]), flush=True)
            return record, stdout.read_text(errors="replace") + stderr.read_text(errors="replace")

        for name in foundation:
            record, _ = compile_target(name)
            if record["exit_status"] or record["timed_out"] or not record["eco_nonempty"]:
                return finish("FOUNDATION_NOT_ACCEPTED", 2, "A counterexample dependency did not independently compile: " + name)
        sanity, sanity_log = compile_target(SANITY)
        if not semantic_rejection(sanity, sanity_log, SANITY) or "cannot prove goal (strict)" not in sanity_log:
            return finish("SANITY_NOT_ESTABLISHED", 2, "Boundary-free contradiction control was not rejected at the intended goal")
        boundary, _ = compile_target("BeeKemKiInterface.eca")
        if boundary["exit_status"] or boundary["timed_out"] or not boundary["eco_nonempty"]:
            return finish("BOUNDARY_NOT_CHECKED", 2, "The original imported interface did not compile")
        contradiction, log = compile_target(CONTRADICTION)
        if contradiction["exit_status"] == 0 and contradiction["eco_nonempty"] and not contradiction["timed_out"]:
            return finish("INCONSISTENT_IMPORTED_BOUNDARY", 1, "The existing imported boundary derives false; security acceptance is blocked")
        if semantic_rejection(contradiction, log, CONTRADICTION):
            # Elaborate the ACTUAL imported theorem with several concrete actors.
            # These are interface-admission controls, not asserted security proofs.
            prefix = """require import AllCore List FSet.
require import BeeKemTypes BeeKemProtocol BeeKemKiGame BeeKemConstruction.
require BeeKemKiInterface.
clone import BeeKemKiInterface as CheckedPaper.
module Oracle = BeeKemKiOracles(BeeKemProtocolOfPaperInstance(PublishedBeeKemInstance)).
module Environment = BeeKemOracleEnvironment(BeeKemProtocolOfPaperInstance(PublishedBeeKemInstance)).
"""
            suffix = """
lemma imported_contract_accepts_this_actor &m
    (users : beekem_user list) (group : beekem_group)
    (membership : beekem_dgm) : true.
proof.
  have H := beekem_theorem1_imported_normalized
    Actor &m users group 1 0 2 1 membership.
  trivial.
qed.
"""
            actors = {
                "ConstantGuess": (True, "proc attack() : bool = { return false; }"),
                "AllSuppliedOracles": (True, """proc attack() : bool = {
  var ok : bool;
  var secret : beekem_secret_output;
  var snapshot : beekem_member_state option;
  var control : beekem_generated_message option;
  var direct : beekem_direct_message option;
  ok <@ O.create_group(BeeKemUser 0, fset1 (BeeKemUser 0));
  ok <@ O.add_member(BeeKemUser 0, BeeKemUser 1);
  ok <@ O.remove_member(BeeKemUser 0, BeeKemUser 1);
  ok <@ O.send_update(BeeKemUser 0);
  ok <@ O.deliver(BeeKemUser 0, BeeKemCounter 1, BeeKemUser 1);
  secret <@ O.reveal(BeeKemUser 0, BeeKemCounter 1);
  secret <@ O.challenge(BeeKemUser 0, BeeKemCounter 2);
  snapshot <@ O.compromise(BeeKemUser 0);
  control <@ O.get_control_message(BeeKemUser 0, BeeKemCounter 1);
  direct <@ O.get_direct_message(BeeKemUser 0, BeeKemCounter 1, BeeKemUser 1);
  return false;
}"""),
                "HiddenBitRead": (False, "proc attack() : bool = { return Oracle.hidden_bit; }"),
                "HiddenBitWrite": (False, "proc attack() : bool = { Oracle.hidden_bit <- true; return true; }"),
                "ProtocolStateRead": (False, "proc attack() : bool = { return Environment.state.`bps_challenge_count = 0; }"),
                "ProtocolStateWrite": (False, "proc attack() : bool = { Environment.state <- Environment.state; return false; }"),
                "BypassSuppliedOracle": (False, "proc attack() : bool = { var s : beekem_member_state option; s <@ Oracle.compromise(BeeKemUser 0); return false; }"),
            }
            result["admission_controls"] = {}
            for name, (allowed, body) in actors.items():
                target = "BoundaryAdmission" + name + ".ec"
                (work / target).write_text(prefix + "module Actor(O : BEEKEM_KI_ORACLES) = {\n" + body + "\n}.\n" + suffix)
                shutil.copyfile(work / target, copies / target)
                result["source_sha256"][target] = sha256(work / target)
                record, text = compile_target(target)
                if allowed:
                    accepted = record["exit_status"] == 0 and record["eco_nonempty"] and not record["timed_out"]
                else:
                    critical = text[text.rfind("[critical]"):]
                    accepted = (record["exit_status"] == 1 and not record["eco_nonempty"] and not record["timed_out"]
                        and "not allowed to use" in critical
                        and ("BeeKemKiOracles" in critical or "BeeKemOracleEnvironment" in critical))
                result["admission_controls"][name] = {"expected_allowed": allowed, "expected_result_observed": accepted}
                if not accepted:
                    return finish("ADMISSION_CONTROL_FAILURE", 2, "Unexpected interface-admission result: " + name)
            return finish("REPRODUCER_REJECTED", 0, "Known contradiction and five private-state bypasses rejected; two legitimate oracle-only actors admitted. This is not a general consistency proof")
        return finish("INCONCLUSIVE_DIAGNOSTIC_FAILURE", 2, "Timeout, malformed proof, missing dependency, or unrecognized failure is not an accepted negative control")


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, subprocess.SubprocessError, ValueError) as error:
        print("Imported-boundary diagnostic infrastructure failure: " + str(error), file=sys.stderr)
        raise SystemExit(2)
