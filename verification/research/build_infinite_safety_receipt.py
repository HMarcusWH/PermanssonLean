"""Verify D-SAFETY sources and record actual compiler and axiom evidence."""
from __future__ import annotations
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

from build_solver_stationary_receipt import recheck, sha

ROOT = Path(__file__).resolve().parents[2]
PREFIX = "PermanssonResearch.ReverseSolver."
MODULES = ["InfiniteSafetyBellman", "BehavioralInfiniteLaw", "InfiniteSafetyFiniteEvaluation",
           "InfiniteSafetyPathSemantics", "GreatestControlledInvariant", "InfiniteSafetyOptimality",
           "InfiniteSafetyLeakage", "InfiniteSafetyAudit"]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AUDIT_COUNT = 15


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--recheck", action="store_true")
    parser.add_argument("--recheck-audit", action="store_true")
    parser.add_argument("--output-dir", type=Path, default=Path("research/paper_closures"))
    args = parser.parse_args()
    output = (ROOT / args.output_dir).resolve()
    if not output.is_relative_to(ROOT):
        raise RuntimeError("Receipt output must remain inside the repository")
    builder = Path(__file__).resolve()
    helper = builder.with_name("build_solver_stationary_receipt.py")
    before = {str(path): sha(path) for path in (builder, helper)}
    records = []
    for name in MODULES:
        module = PREFIX + name
        source = ROOT / Path(*module.split(".")).with_suffix(".lean")
        artifact = ROOT / ".lake/build/lib/lean" / Path(*module.split(".")).with_suffix(".olean")
        logdir = ROOT / ".lake/closure-build"
        status_path = logdir / (module + ".json")
        status = json.loads(status_path.read_text(encoding="utf-8")) if status_path.exists() else {}
        fresh = (status.get("status") == "PASS" and status.get("returncode") == 0
                 and artifact.exists() and (logdir / (module + ".out")).exists()
                 and artifact.stat().st_mtime_ns >= source.stat().st_mtime_ns
                 and source.stat().st_mtime <= status.get("started", 0)
                 and status.get("source_sha256_after", sha(source)) == sha(source)
                 and status.get("olean_sha256", sha(artifact)) == sha(artifact))
        if args.recheck or not fresh or (args.recheck_audit and name == "InfiniteSafetyAudit"):
            status = recheck(module, source, artifact)
        if status.get("status") != "PASS" or status.get("returncode") != 0:
            raise RuntimeError(f"Actual compiler check failed: {module}: {status}")
        if artifact.stat().st_mtime_ns < source.stat().st_mtime_ns:
            raise RuntimeError(f"Compiled artifact predates source: {module}")
        records.append({"module": module, "source": source.relative_to(ROOT).as_posix(),
                        "source_sha256": sha(source), "olean_sha256": sha(artifact), "compiler": status})
    audit = (ROOT / ".lake/closure-build" / (PREFIX + "InfiniteSafetyAudit.out")).read_text(encoding="utf-8")
    groups = re.findall(r"depends on axioms:\s*\[(.*?)\]", audit, re.S)
    if len(groups) + audit.count("does not depend on any axioms") != AUDIT_COUNT:
        raise RuntimeError("Incomplete actual printed transitive axiom audit")
    found = {word.strip() for group in groups for word in group.split(",") if word.strip()}
    if not found <= ALLOWED_AXIOMS:
        raise RuntimeError(f"Unexpected transitive axioms: {found - ALLOWED_AXIOMS}")
    for path, digest in before.items():
        if sha(Path(path)) != digest:
            raise RuntimeError("Receipt code changed during execution")
    for record in records:
        source = ROOT / record["source"]
        artifact = ROOT / ".lake/build/lib/lean" / Path(*record["module"].split(".")).with_suffix(".olean")
        if sha(source) != record["source_sha256"] or sha(artifact) != record["olean_sha256"]:
            raise RuntimeError(f"Inputs changed during receipt: {record['module']}")
    output.mkdir(parents=True, exist_ok=True)
    audit_file = output / "infinite_safety_axioms.txt"
    audit_file.write_text(audit, encoding="utf-8")
    head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
    dirty = bool(subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT, text=True).strip())
    receipt = {
        "scope": "D2-P07 D-SAFETY: actual infinite safety over all real full-history behavioral controllers",
        "status": "THEOREM_FORMALIZED",
        "source_H": None, "synthetic_S": None, "eventual_merge_M": None,
        "recording_head": head, "recording_worktree_dirty": dirty,
        "base_B": "39279799834ae536bda715dedecdc11a32bf6c82",
        "builder_sha256": before[str(builder)], "compiler_helper_sha256": before[str(helper)],
        "modules": records,
        "actual_path_law": "Normalized countable realized-control/physical-history kernel, canonical infinite trajectory, almost-sure chronological history consistency",
        "event": "All physical states, including time zero, lie in G forever",
        "policy_class": "Every real BehavioralPolicy on the complete realized control and state history",
        "proved": ["bounded decreasing finite values and actual convergence", "limiting finite-sum/finite-max Bellman fixed point",
                   "all-behavioral actual infinite-event probability upper bound", "one deterministic stationary selector attains simultaneously for every initial state",
                   "rational descending controlled-invariant iteration stabilizes by |G|", "computed core equals the value-one set",
                   "fixed positive leakage tends to zero; actual 99/100 finite-survival example has zero infinite safety"],
        "signature_and_axiom_audit": {"output": audit_file.relative_to(ROOT).as_posix(),
                                      "sha256": sha(audit_file), "reports": AUDIT_COUNT,
                                      "allowed_axioms": sorted(ALLOWED_AXIOMS), "observed_axioms": sorted(found)},
        "boundaries": ["Controlled-process theorem; no C70 frozen-intervention claim without an explicit typing/law bridge",
                       "The limiting real value and stationary argmax are mathematical noncomputable objects; the controlled-invariant iteration is exact rational and finite",
                       "No substitution of finite survival for infinite retention"],
    }
    destination = output / "infinite_safety_receipt.json"
    destination.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")
    print(f"PASS D-SAFETY: {len(records)} modules, {AUDIT_COUNT} actual axiom reports; {destination}")


if __name__ == "__main__":
    main()
