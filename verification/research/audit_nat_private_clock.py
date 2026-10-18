"""Source-bound natural-clock compilation, semantic falsifier and axiom audit."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import time

from test_x1_paper_closure import ALLOWED, declaration_names, sha256, changed_files, classify_mutation

ROOT = Path(__file__).resolve().parents[2]
MODULES = ["PermanssonResearch.MultiAgent.NatPrivateClock",
           "PermanssonResearch.MultiAgent.NatPrivateClockTransport"]
FIXTURE = ROOT / "verification/research/MultiAgentNatPrivateClock.lean"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("PERMANSSON_X1_LEAN"))
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    command = [args.lean] if args.lean else ["lake", "env", "lean"]
    scratch = ROOT / ".lake/nat-private-clock-closure"
    scratch.mkdir(parents=True, exist_ok=True)
    sources = [ROOT / (name.replace(".", "/") + ".lean") for name in MODULES]
    inputs = sources + [FIXTURE, Path(__file__),
        Path(__file__).with_name("test_paper_nat_private_clock_lean.py"),
        Path(__file__).with_name("test_x1_paper_closure.py")]
    hashes = {path.relative_to(ROOT).as_posix(): sha256(path) for path in inputs}
    receipt = {"status": "RUNNING", "source_sha256": hashes, "modules": MODULES,
               "scope": "Countable measurable strategic coordinates S0/S1/S2 with measurable singletons; finite measurable X/A1/A2; actual unbounded private clock Nat with successor update and arbitrary declared Nat-indexed anchors. No arbitrary measurable-coordinate extension is claimed here.",
               "compiler_command": command, "positive_controls": {}, "mutations": {},
               "compiled_artifacts": {}, "axiom_audit": {}}
    receipt_path = scratch / "receipt.json"

    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")

    def run(label, arguments):
        print("Checking", label, flush=True)
        started = time.monotonic()
        try:
            cp = subprocess.run(command + arguments, cwd=ROOT, capture_output=True,
                text=True, encoding="utf-8", timeout=args.timeout)
            output, code = cp.stdout + cp.stderr, cp.returncode
        except (subprocess.TimeoutExpired, OSError) as exc:
            output, code = str(exc), None
        (scratch / (label + ".out")).write_text(output, encoding="utf-8")
        return output, code, time.monotonic()-started

    save()
    for module, source in zip(MODULES, sources):
        artifact = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        artifact.parent.mkdir(parents=True, exist_ok=True)
        output, code, elapsed = run(module, ["-o", str(artifact), str(source.relative_to(ROOT))])
        ok = code == 0 and artifact.is_file() and not re.search(r"error(?:\([^)]*\))?:|declaration uses .sorry.", output)
        receipt["positive_controls"][module] = {"status": "PASS" if ok else "FAIL",
            "returncode": code, "elapsed": elapsed}
        if ok:
            receipt["compiled_artifacts"][artifact.relative_to(ROOT).as_posix()] = sha256(artifact)
        save()
        if not ok:
            receipt.update(status="POSITIVE_CONTROL_FAILED")
            save()
            return 1
    output, code, elapsed = run("fixture", [str(FIXTURE)])
    ok = code == 0 and not re.search(r"error(?:\([^)]*\))?:|declaration uses .sorry.", output)
    receipt["positive_controls"]["fixture"] = {"status": "PASS" if ok else "FAIL",
        "returncode": code, "elapsed": elapsed}
    save()
    if not ok:
        receipt.update(status="POSITIVE_CONTROL_FAILED")
        save()
        return 1

    text = FIXTURE.read_text(encoding="utf-8")
    old = "{NatPrivateClock.lift 0 start} = 0 := by"
    assert text.count(old) == 1
    negative = scratch / "frozen_clock.lean"
    negative.write_text(text.replace(old, "{NatPrivateClock.lift 0 start} = 1 := by"),
                        encoding="utf-8", newline="\n")
    output, code, elapsed = run("frozen_clock", [str(negative)])
    result = classify_mutation("corrupt_denominator", code, output) if code is not None else {
        "status": "INVALID_ENVIRONMENT", "returncode": None}
    result.update(elapsed=elapsed, mutation_sha256=sha256(negative))
    receipt["mutations"]["frozen_clock"] = result
    save()

    names = [name for source in sources + [FIXTURE]
             for name in declaration_names(source.read_text(encoding="utf-8"))]
    audit = scratch / "axiom_audit.lean"
    audit.write_text(text + "\n" +
        "".join(f"#print axioms {name}\n" for name in names), encoding="utf-8")
    output, code, elapsed = run("axiom_audit", [str(audit)])
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    clean = re.findall(r"'([^']+)' does not depend on any axioms", output)
    missing = sorted(set(names) - ({name for name, _ in found} | set(clean)))
    forbidden = {name: sorted({a.strip() for a in used.replace("\n", " ").split(",")
        if a.strip()} - ALLOWED) for name, used in found}
    forbidden = {name: used for name, used in forbidden.items() if used}
    audit_ok = code == 0 and not missing and not forbidden
    receipt["axiom_audit"] = {"status": "PASS" if audit_ok else "FAIL", "returncode": code,
        "elapsed": elapsed, "declarations": len(names), "declaration_names": names,
        "missing": missing, "forbidden": forbidden}
    changed = changed_files(hashes) + changed_files(receipt["compiled_artifacts"])
    receipt.update(changed_files=changed,
        status="PASS" if audit_ok and result["status"] == "REJECTED" and not changed else "FAIL")
    save()
    print(json.dumps(receipt, indent=2), flush=True)
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
