"""Source-hashed transitive axiom audit for the finite multiagent closures.

Compile each selected module before running this audit. The receipt records
source hashes and requires a newer compiled artifact, then asks Lean to inspect
every source-named declaration. Only Lean's standard proof axioms are allowed.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEFAULT = ["AutonomousKey", "AutonomousSupportClosure", "StrictMA2Obstruction",
           "AutonomousMarkedKernel", "PlayerTwoProtocols", "PlayerSwapTransport",
           "PlayerSwapConstitution", "BehavioralAutonomy", "ChronologicalPathLaw",
           "PrivateClock", "PrivateClockTransport", "FiniteProductProtocols", "FiniteProductTwo"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECL = re.compile(r"(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:({\[]+)")


def declaration_names(source: str) -> list[str]:
    scopes: list[tuple[str, str]] = []
    names = []
    for line in source.splitlines():
        if line.startswith("namespace "):
            scopes.append(("namespace", line.split()[1]))
        elif line.startswith("section") and (line == "section" or line.startswith("section ")):
            scopes.append(("section", line[7:].strip()))
        elif line == "end" or line.startswith("end "):
            kind, name = scopes.pop()
            if line != "end":
                assert name == line.split()[1], (name, line)
        elif match := DECL.match(line):
            names.append(".".join([name for kind, name in scopes if kind == "namespace"]
                                  + [match.group(1)]))
    assert not scopes
    return names


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", help="Pinned compiler executable; use caller's LEAN_PATH")
    parser.add_argument("--module", action="append", help="MultiAgent module basename; repeatable")
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    modules = args.module or DEFAULT
    scratch = ROOT / ".lake/multiagent-paper-closure"
    scratch.mkdir(parents=True, exist_ok=True)
    command = [args.lean] if args.lean else ["lake", "env", "lean"]
    sources = {name: ROOT / f"PermanssonResearch/MultiAgent/{name}.lean" for name in modules}
    receipt = {"modules": modules, "source_sha256": {}, "artifacts_current": {},
               "compiler_command": command, "status": "RUNNING"}
    names = []
    for name, path in sources.items():
        receipt["source_sha256"][str(path.relative_to(ROOT))] = hashlib.sha256(path.read_bytes()).hexdigest()
        artifact = ROOT / f".lake/build/lib/lean/PermanssonResearch/MultiAgent/{name}.olean"
        receipt["artifacts_current"][name] = artifact.exists() and artifact.stat().st_mtime >= path.stat().st_mtime
        names.extend(declaration_names(path.read_text(encoding="utf-8")))
    receipt_path = scratch / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    if not all(receipt["artifacts_current"].values()):
        receipt["status"] = "STALE_OR_MISSING_ARTIFACT"
        receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
        print(json.dumps(receipt, indent=2), flush=True)
        return 1
    audit = scratch / "axiom_audit.lean"
    audit.write_text("".join(f"import PermanssonResearch.MultiAgent.{m}\n" for m in modules)
                     + "".join(f"#print axioms {n}\n" for n in names), encoding="utf-8")
    started = time.monotonic()
    run = subprocess.run(command + [str(audit)], cwd=ROOT, capture_output=True,
                         text=True, encoding="utf-8", timeout=args.timeout)
    output = run.stdout + run.stderr
    (scratch / "axiom_audit.out").write_text(output, encoding="utf-8")
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    clean = re.findall(r"'([^']+)' does not depend on any axioms", output)
    missing = sorted(set(names) - ({n for n, _ in found} | set(clean)))
    forbidden = {n: sorted({a.strip() for a in used.replace("\n", " ").split(",") if a.strip()} - ALLOWED)
                 for n, used in found}
    forbidden = {n: used for n, used in forbidden.items() if used}
    ok = run.returncode == 0 and not missing and not forbidden
    receipt.update(status="PASS" if ok else "FAIL", returncode=run.returncode,
                   declarations=len(names), elapsed=time.monotonic()-started,
                   missing=missing, forbidden=forbidden)
    receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(json.dumps(receipt, indent=2), flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
