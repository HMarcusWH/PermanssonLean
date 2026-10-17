"""Declaration-level transitive audit for the D2 finite residence objective."""
import os
import re
import subprocess
import sys
import tempfile
from pathlib import Path

MODULES = [
    "PermanssonResearch/ReverseSolver/ResidenceEvent.lean",
    "PermanssonResearch/ReverseSolver/ResidenceValue.lean",
    "PermanssonResearch/ReverseSolver/ResidenceContracts.lean",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:({]+)"
)


def declarations(source):
    stack, found = [], []
    for line in source.splitlines():
        line = line.strip()
        if line.startswith("namespace "):
            stack.append(line.split()[1])
        elif line.startswith("end ") and stack:
            if line.split()[1] == stack[-1]:
                stack.pop()
        elif re.match(r"(?:@\[[^\]]*\]\s*)?private\s+", line):
            raise ValueError("Private declarations cannot be silently omitted")
        elif re.match(r"(?:noncomputable\s+)?instance\s*(?::|\()", line):
            raise ValueError("Anonymous instances cannot be silently omitted")
        elif match := DECL.match(line):
            found.append(".".join(stack + [match.group(1)]))
    return found


def main():
    root = Path(__file__).resolve().parents[2]
    names = [name for path in MODULES
             for name in declarations((root / path).read_text(encoding="utf-8"))]
    if not names or len(names) != len(set(names)):
        raise ValueError("Empty or duplicate declaration discovery")
    source = "import PermanssonResearch.ReverseSolver.ResidenceContracts\n"
    source += "".join(f"#print axioms {name}\n" for name in names)
    with tempfile.TemporaryDirectory() as scratch:
        path = Path(scratch) / "AuditD2.lean"
        path.write_text(source, encoding="utf-8")
        proc = subprocess.run(["lake", "env", "lean", str(path)], cwd=root,
                              capture_output=True, text=True, encoding="utf-8")
    output = proc.stdout + proc.stderr
    if proc.returncode or re.search(r"(?m)^.*error", output):
        print(output)
        return 1
    used = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
    free = re.findall(r"'([^']+)' does not depend on any axioms", output)
    seen = {name for name, _ in used} | set(free)
    bad = [(name, axioms) for name, axioms in used
           if not {a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()} <= ALLOWED]
    if set(names) != seen or bad:
        print(output)
        print(f"missing={set(names)-seen}; forbidden={bad}")
        return 1
    print(f"D2 axiom audit PASS: {len(names)} declarations; only the three standard axioms")
    return 0


if __name__ == "__main__":
    sys.exit(main())
