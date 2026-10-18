"""Build a fail-closed receipt from actual pinned-compiler logs and artifacts."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
MODULES = [
    "FiniteMonitor", "BehavioralFinitePolicy", "MonitorOptimality",
    "ChronologicalFiniteLaw", "ChronologicalMonitorMeasure", "MonitorHistoryBridge",
    "ComputableFiniteMonitor", "CompactResidenceMonitor", "FirstEntryMonitor",
    "AvoidResidenceMonitor", "AvoidResidenceHistoryBridge", "MonitorEventOptimality",
    "ResidenceSpecializationOptimality", "SolverBoundaryWitnesses",
    "C11ReferenceMatrix", "C11ReferenceProbability", "C11ReferenceClasses",
    "C11ReferenceStationaryFamily", "C11ReferenceExamples", "C11ReferenceTypedBridge",
    "RectangularFiniteGame", "RectangularGameLaw",
    "StationaryOccupationObjective", "StationaryMenuOptimization",
    "RollingMonitorTable", "RollingResidenceTable",
    "InitialLawMonitor",
    "SolverClosureAudit",
]
PREFIX = "PermanssonResearch.ReverseSolver."
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def recheck(module: str, source: Path, artifact: Path) -> dict:
    """Run the repository's pinned compiler and bind the exact input/output."""
    lake = shutil.which("lake")
    if lake is None:
        raise RuntimeError("The pinned Lean/Lake toolchain must be installed and on PATH")
    env = dict(os.environ, LEAN_NUM_THREADS="2")
    version = subprocess.run([lake, "env", "lean", "--version"], cwd=ROOT, env=env,
                             capture_output=True, text=True, encoding="utf-8", timeout=180)
    toolchain = (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip()
    expected = re.search(r":v?(\d+\.\d+\.\d+)", toolchain)
    actual = re.search(r"\bversion\s+([^,\s)]+)", version.stdout)
    if (version.returncode != 0 or expected is None or actual is None
            or expected.group(1) != actual.group(1)):
        raise RuntimeError(f"Pinned compiler verification failed: {version.stdout}{version.stderr}")
    logdir = ROOT / ".lake/closure-build"
    logdir.mkdir(parents=True, exist_ok=True)
    artifact.parent.mkdir(parents=True, exist_ok=True)
    command = [lake, "env", "lean", "-o", str(artifact.relative_to(ROOT)),
               str(source.relative_to(ROOT))]
    before = sha(source)
    started = time.time()
    status = {"module": module, "started": started, "status": "RUNNING",
              "command": command, "compiler_version": version.stdout.strip(),
              "toolchain": toolchain, "source_sha256_before": before}
    status_path = logdir / (module + ".json")
    status_path.write_text(json.dumps(status), encoding="utf-8")
    print(f"Checking {module}", flush=True)
    with (logdir / (module + ".out")).open("w", encoding="utf-8") as out:
        try:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=out,
                                    stderr=subprocess.STDOUT, timeout=900)
            after = sha(source)
            passed = result.returncode == 0 and before == after and artifact.exists()
            status.update(status="PASS" if passed else "FAIL", returncode=result.returncode,
                          elapsed=time.time()-started, source_sha256_after=after)
            if passed:
                status["olean_sha256"] = sha(artifact)
        except subprocess.TimeoutExpired:
            status.update(status="TIMEOUT", elapsed=time.time()-started)
    status_path.write_text(json.dumps(status), encoding="utf-8")
    return status


def main() -> None:
    builder_before = sha(Path(__file__).resolve())
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--recheck", action="store_true",
                        help="re-run all pinned Lean checks, including the printed axiom audit")
    parser.add_argument("--recheck-audit", action="store_true",
                        help="always compile the actual signature/axiom audit, reusing fresh dependency checks")
    parser.add_argument("--output-dir", type=Path, default=Path("research/paper_closures"),
                        help="repository-local output directory (CI should choose a directory under .lake)")
    args = parser.parse_args()
    output_dir = (ROOT / args.output_dir).resolve()
    if not output_dir.is_relative_to(ROOT):
        raise RuntimeError("The receipt output directory must be inside the repository")
    records = []
    for short in MODULES:
        module = PREFIX + short
        source = ROOT / Path(*module.split(".")).with_suffix(".lean")
        artifact = ROOT / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
        status_path = ROOT / ".lake/closure-build" / (module + ".json")
        status = (json.loads(status_path.read_text(encoding="utf-8"))
                  if status_path.exists() else {})
        fresh = (status.get("status") == "PASS" and status.get("returncode") == 0
                 and (ROOT / ".lake/closure-build" / (module + ".out")).exists()
                 and artifact.exists() and artifact.stat().st_mtime_ns >= source.stat().st_mtime_ns
                 and source.stat().st_mtime <= status.get("started", 0)
                 and status.get("source_sha256_after", sha(source)) == sha(source)
                 and status.get("olean_sha256", sha(artifact)) == sha(artifact))
        if args.recheck or not fresh or (args.recheck_audit and short == "SolverClosureAudit"):
            status = recheck(module, source, artifact)
        if status.get("status") != "PASS" or status.get("returncode") != 0:
            raise RuntimeError(f"No successful actual compiler result for {module}: {status}")
        if artifact.stat().st_mtime_ns < source.stat().st_mtime_ns:
            raise RuntimeError(f"Artifact predates final source: {module}")
        if status.get("source_sha256_after", sha(source)) != sha(source):
            raise RuntimeError(f"Source changed after compilation: {module}")
        records.append({"module": module, "source": source.relative_to(ROOT).as_posix(),
                        "source_sha256": sha(source), "olean_sha256": sha(artifact),
                        "compiler": status})
    audit_path = ROOT / ".lake/closure-build" / (PREFIX + "SolverClosureAudit.out")
    audit = audit_path.read_text(encoding="utf-8")
    dependencies = re.findall(r"depends on axioms:\s*\[(.*?)\]", audit, re.S)
    if len(dependencies) + audit.count("does not depend on any axioms") < 22:
        raise RuntimeError("Incomplete printed transitive axiom audit")
    found = {name.strip() for group in dependencies for name in group.split(",") if name.strip()}
    if not found <= ALLOWED_AXIOMS:
        raise RuntimeError(f"Unexpected transitive axioms: {found - ALLOWED_AXIOMS}")
    if sha(Path(__file__).resolve()) != builder_before:
        raise RuntimeError("The receipt builder changed during execution")
    for record in records:
        source = ROOT / record["source"]
        artifact = ROOT / ".lake/build/lib/lean" / Path(*record["module"].split(".")).with_suffix(".olean")
        if sha(source) != record["source_sha256"] or sha(artifact) != record["olean_sha256"]:
            raise RuntimeError(f"Source or compiled artifact changed during receipt generation: {record['module']}")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True).strip())
    audit_destination = output_dir / "solver_stationary_axioms.txt"
    audit_destination.parent.mkdir(parents=True, exist_ok=True)
    audit_destination.write_text(audit, encoding="utf-8")
    receipt = {
        "scope": "U05/U06 finite monitor and literal residence specializations; U07 C11 reference family; D-ROBUST realized-control rectangular game; D-CLASS stationary-menu occupation functional",
        "status": "SCOPED_THEOREM_FORMALIZED",
        "source_H": None, "recording_head": head, "recording_worktree_dirty": dirty,
        "base_B": "39279799834ae536bda715dedecdc11a32bf6c82",
        "synthetic_S": None, "eventual_merge_M": None,
        "receipt_builder_sha256": builder_before,
        "modules": records,
        "signature_and_axiom_audit": {"output": audit_destination.relative_to(ROOT).as_posix(),
                                       "sha256": sha(audit_destination), "axioms": sorted(found),
                                       "declarations_audited": len(dependencies) + audit.count("does not depend on any axioms")},
        "selected_contracts": {
            "D-MONITOR": "Normalized chronological real behavioral state/control law with arbitrary real initial law; monitor pushforward; upper bound and actual deterministic time/state/monitor attainer simultaneous over all initial states; executable rational reference value and fixed-order tie selection.",
            "D-RESIDENCE": "Finite capped streak and completed flag; exact original entry-by-T event on horizon T+m; real behavioral optimum and actual deterministic HistoryPolicy probability bridge; array-backed backwards tables with exactly n by 2*(m+2) cells and lookup equivalence to the exact rational optimum.",
            "D-FIRST": "Finite waiting/active/failed/succeeded phases; first-target-only literal block semantics and real behavioral optimum; retry counterexample.",
            "D-AVOID": "Finite streak/success/failure state; danger precedence before success; danger after success retained; literal block semantics and real behavioral optimum plus actual HistoryPolicy probability bridge.",
            "C11-REFERENCE": "Total rational Cramer family constructor on genuine computed bottom classes, without a certificate correctness premise; checker accepts every nonempty rational stochastic input.",
            "D-ROBUST-realized-control": "Actual normalized chronological game law; real behavioral controller/nature histories; nature observes realized control and chooses a row independently at every node; deterministic time-state saddle strategies attain the rational max-min value.",
            "D-CLASS": "Exact rational C10/C11 evaluation equals the expected predeclared bounded functional of the genuine random descriptor occupation limit; all admissible deterministic stationary state-feedback policies are enumerated and a lexicographically tie-broken exact maximizer attains the actual expectation optimum.",
        },
        "residual_scope": [
            "No arbitrary adaptive asymptotic policy theorem is asserted.",
            "D-LP, D-BELIEF, D-SAFETY and D-BLOCK are not closed by the boundary witnesses in this module set.",
            "The D-ROBUST private-control-draw stage maximin LP and whole-horizon hidden-model commitment are separate; only the realized-control-observing rectangular game is certified here.",
            "The executable scalar recursion and array-backed backwards tables are certified; no formal runtime, memory, or bit-complexity theorem is claimed.",
            "C-P01 nonfinite occupation contracts are separate from C11-REFERENCE.",
        ],
    }
    destination = output_dir / "solver_stationary_receipt.json"
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(destination)


if __name__ == "__main__":
    main()
