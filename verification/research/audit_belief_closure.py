"""Source-hashed audit of all named declarations in the finite belief closure.

Run after building the six research modules. Import, elaboration, timeout, stale
artifact, missing-declaration, and nonstandard-axiom failures all fail the audit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import time


ROOT = Path(__file__).resolve().parents[2]
MODULES = ["BeliefKernel", "BeliefAlpha", "BeliefHistory", "BeliefFilter",
           "BeliefChronology", "BeliefMonitor"]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECL = re.compile(r"(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:({\[]+)")


def declaration_names(source: str) -> list[str]:
    scopes: list[tuple[str, str]] = []
    names = []
    for line in source.splitlines():
        if line.startswith("namespace "):
            scopes.append(("namespace", line.split()[1]))
        elif re.fullmatch(r"(?:noncomputable )?section(?: \S+)?", line):
            scopes.append(("section", line.partition("section")[2].strip()))
        elif line == "end" or line.startswith("end "):
            _, name = scopes.pop()
            if line != "end":
                assert name == line.split()[1], (name, line)
        elif match := DECL.match(line):
            names.append(".".join([name for kind, name in scopes if kind == "namespace"]
                                  + [match.group(1)]))
    assert not scopes, scopes
    assert names and len(names) == len(set(names))
    return names


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", help="Pinned Lean executable, using the caller's LEAN_PATH")
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    scratch = ROOT / ".lake/belief-paper-closure"
    scratch.mkdir(parents=True, exist_ok=True)
    command = [args.lean] if args.lean else ["lake", "env", "lean"]
    sources = {name: ROOT / f"PermanssonResearch/ReverseSolver/{name}.lean" for name in MODULES}
    receipt = {"modules": MODULES, "source_sha256": {}, "artifacts_current": {},
               "compiler_command": command, "status": "RUNNING"}
    names = []
    for name, path in sources.items():
        receipt["source_sha256"][str(path.relative_to(ROOT))] = digest(path)
        artifact = ROOT / f".lake/build/lib/lean/PermanssonResearch/ReverseSolver/{name}.olean"
        receipt["artifacts_current"][name] = artifact.exists() and artifact.stat().st_mtime >= path.stat().st_mtime
        names.extend(declaration_names(path.read_text(encoding="utf-8")))
    receipt_path = scratch / "receipt.json"

    def save() -> None:
        receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")

    save()
    if not all(receipt["artifacts_current"].values()):
        receipt["status"] = "STALE_OR_MISSING_ARTIFACT"
        save()
        print(json.dumps(receipt, indent=2), flush=True)
        return 1
    audit = scratch / "axiom_audit.lean"
    audit.write_text("".join(f"import PermanssonResearch.ReverseSolver.{m}\n" for m in MODULES)
                     + "".join(f"#print axioms {n}\n" for n in names), encoding="utf-8")
    receipt["audit_sha256"] = digest(audit)
    started = time.monotonic()
    try:
        run = subprocess.run(command + [str(audit)], cwd=ROOT, capture_output=True,
                             text=True, encoding="utf-8", timeout=args.timeout)
        output = run.stdout + run.stderr
        code = run.returncode
    except (subprocess.TimeoutExpired, OSError) as exc:
        output = str(exc)
        code = None
    (scratch / "axiom_audit.out").write_text(output, encoding="utf-8")
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    clean = re.findall(r"'([^']+)' does not depend on any axioms", output)
    missing = sorted(set(names) - ({n for n, _ in found} | set(clean)))
    forbidden = {n: sorted({a.strip() for a in used.replace("\n", " ").split(",") if a.strip()} - ALLOWED)
                 for n, used in found}
    forbidden = {n: used for n, used in forbidden.items() if used}
    changed = [str(path.relative_to(ROOT)) for path in sources.values()
               if digest(path) != receipt["source_sha256"][str(path.relative_to(ROOT))]]
    ok = code == 0 and not missing and not forbidden and not changed
    receipt.update(status="PASS" if ok else "FAIL", returncode=code,
                   declarations=len(names), declaration_names=names,
                   elapsed=time.monotonic()-started, missing=missing,
                   forbidden=forbidden, changed_during_check=changed)
    save()
    print(json.dumps(receipt, indent=2), flush=True)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
