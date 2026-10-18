"""Audit the stationary random-law closure's public declarations and private dependencies.

All eight mathematical modules must have current compiled artifacts. Each public
source-named declaration is inspected by Lean's transitive axiom printer.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time

from audit_belief_closure import declaration_names


ROOT = Path(__file__).resolve().parents[2]
MODULES = ["PermanssonResearch.MultipleLimit.StationaryCanonicalShift",
           "PermanssonResearch.MultipleLimit.StationaryConditionalLaw",
           "PermanssonResearch.MultipleLimit.CanonicalInitialAbsoluteContinuity",
           "PermanssonResearch.MultipleLimit.CanonicalInitialDensity",
           "PermanssonResearch.MultipleLimit.StationaryRandomOccupation",
           "PermanssonResearch.MultipleLimit.CountableEmpiricalWeak",
           "PermanssonResearch.MultipleLimit.StationaryConditionalInvariant",
           "PermanssonResearch.MultipleLimit.PolishStationaryRandomOccupation"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean")
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    scratch = ROOT / ".lake/stationary-random-closure"
    scratch.mkdir(parents=True, exist_ok=True)
    command = [args.lean] if args.lean else ["lake", "env", "lean"]
    sources = {m: ROOT / (m.replace(".", "/") + ".lean") for m in MODULES}
    receipt = {"modules": MODULES, "source_sha256": {}, "artifacts_current": {},
               "compiler_command": command, "status": "RUNNING",
               "scope": "All public source-named declarations; private helpers inspected transitively"}
    names = []
    for name, source in sources.items():
        receipt["source_sha256"][str(source.relative_to(ROOT))] = digest(source)
        artifact = ROOT / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")
        receipt["artifacts_current"][name] = artifact.exists() and artifact.stat().st_mtime >= source.stat().st_mtime
        names.extend(declaration_names(source.read_text(encoding="utf-8")))
    receipt_path = scratch / "receipt.json"

    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")

    save()
    if not all(receipt["artifacts_current"].values()):
        receipt["status"] = "STALE_OR_MISSING_ARTIFACT"
        save()
        print(json.dumps(receipt, indent=2), flush=True)
        return 1
    audit = scratch / "axiom_audit.lean"
    audit.write_text("".join(f"import {m}\n" for m in MODULES)
                     + "".join(f"#print axioms {n}\n" for n in names), encoding="utf-8")
    receipt["audit_sha256"] = digest(audit)
    started = time.monotonic()
    try:
        run = subprocess.run(command + [str(audit)], cwd=ROOT, capture_output=True,
                             text=True, encoding="utf-8", timeout=args.timeout)
        output = run.stdout + run.stderr
        code = run.returncode
    except (subprocess.TimeoutExpired, OSError) as exc:
        output, code = str(exc), None
    (scratch / "axiom_audit.out").write_text(output, encoding="utf-8")
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    clean = re.findall(r"'([^']+)' does not depend on any axioms", output)
    missing = sorted(set(names) - ({n for n, _ in found} | set(clean)))
    forbidden = {n: sorted({a.strip() for a in used.replace("\n", " ").split(",") if a.strip()} - ALLOWED)
                 for n, used in found}
    forbidden = {n: used for n, used in forbidden.items() if used}
    changed = [str(p.relative_to(ROOT)) for p in sources.values()
               if digest(p) != receipt["source_sha256"][str(p.relative_to(ROOT))]]
    receipt.update(status="PASS" if code == 0 and not missing and not forbidden and not changed else "FAIL",
                   returncode=code, declarations=len(names), declaration_names=names,
                   missing=missing, forbidden=forbidden, changed_during_check=changed,
                   elapsed=time.monotonic()-started)
    save()
    print(json.dumps(receipt, indent=2), flush=True)
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
