"""Focused transitive axiom audit for the C69 (C-Exit D) declarations.

Every theorem/def declared in the listed research modules is passed to
`#print axioms`; the audit fails unless each depends only on the standard
allowlist {propext, Classical.choice, Quot.sound}. This complements, and does
not replace, the full Research Lean `axiom-audit` of PermanssonResearch.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

MODULES = [
    "PermanssonResearch/RegimeExit/ShiftedPrefixStationarity.lean",
    "PermanssonResearch/RegimeExit/StoppedFutureRestart.lean",
]
NAMESPACE = "PermanssonResearch.RegimeExit"
IMPORT = "PermanssonResearch.RegimeExit.StoppedFutureRestart"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECL = re.compile(r"^(?:theorem|lemma|def|noncomputable def|abbrev)\s+([A-Za-z_0-9.']+)", re.M)


def run_audit(modules, import_module, label) -> int:
    root = Path(__file__).resolve().parents[2]
    decls = []
    for rel in modules:
        decls += DECL.findall((root / rel).read_text(encoding="utf-8"))
    if not decls:
        print("No declarations discovered", file=sys.stderr)
        return 1
    src = f"import {import_module}\n" + "".join(
        f"#print axioms {NAMESPACE}.{d}\n" for d in decls)
    with tempfile.TemporaryDirectory() as tmp:
        f = Path(tmp) / "AuditResearch.lean"
        f.write_text(src, encoding="utf-8")
        run = subprocess.run(["lake", "env", "lean", str(f)], cwd=root,
                             capture_output=True, text=True)
    out = run.stdout + run.stderr
    if run.returncode != 0 or re.search(r"(?m)^.*error", out):
        print(out)
        print("Lean audit invocation failed", file=sys.stderr)
        return 1
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out, re.S)
    clean = re.findall(r"'([^']+)' does not depend on any axioms", out)
    seen = {name for name, _ in found} | set(clean)
    missing = [d for d in decls if f"{NAMESPACE}.{d}" not in seen]
    bad = []
    for name, axioms in found:
        used = {a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()}
        if not used <= ALLOWED:
            bad.append((name, sorted(used - ALLOWED)))
    if missing or bad:
        print(out)
        print(f"missing={missing} forbidden={bad}", file=sys.stderr)
        return 1
    print(f"{label} axiom audit PASS: {len(decls)} declarations, "
          f"{len(found)} with allowlisted axioms, {len(clean)} axiom-free")
    return 0


def main() -> int:
    return run_audit(MODULES, IMPORT, "C69")


if __name__ == "__main__":
    sys.exit(main())
