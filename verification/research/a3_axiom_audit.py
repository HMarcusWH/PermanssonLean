"""Focused transitive axiom audit for the A3 (contractive W1 robustness) declarations.

Every top-level theorem/lemma/def/abbrev/instance/structure/inductive/class in
the listed modules (namespace-aware; attribute-prefixed, `noncomputable` and
`protected` forms included; non-ASCII names included) is passed to
`#print axioms`; each must depend only on {propext, Classical.choice,
Quot.sound}. Anonymous instances and `private` declarations are rejected (they
cannot be addressed by name, so they could not be audited). Complements, and does not replace, the
full Research Lean audit.
"""
import re
import subprocess
import sys
import tempfile
from pathlib import Path

MODULES = [
    "PermanssonResearch/Probability/KantorovichDual.lean",
    "PermanssonResearch/Probability/KantorovichTV.lean",
    "PermanssonResearch/Perturbation/ContractiveOccupation.lean",
    "PermanssonResearch/Perturbation/ContractiveAdversaries.lean",
]
IMPORTS = [
    "PermanssonResearch.Probability.KantorovichTV",
    "PermanssonResearch.Perturbation.ContractiveAdversaries",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
ATTR = r"(?:@\[[^\]]*\]\s*)?"
MODS = r"(?:(?:noncomputable|protected)\s+)*"
DECL = re.compile(ATTR + MODS +
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:({\[]+)")
ANON_INSTANCE = re.compile(ATTR + MODS + r"instance\s*(?::|\(|\[|\{)")
PRIVATE = re.compile(ATTR + r"private\s")
NS = re.compile(r"^namespace\s+(\S+)")
END = re.compile(r"^end\s+(\S+)")


def declarations(text: str):
    stack, out = [], []
    for line in text.splitlines():
        if m := NS.match(line):
            stack.append(m.group(1))
        elif (m := END.match(line)) and stack and stack[-1] == m.group(1):
            stack.pop()
        elif PRIVATE.match(line):
            raise SystemExit(f"private declaration (cannot be audited by name): {line!r}")
        elif ANON_INSTANCE.match(line):
            raise SystemExit(f"anonymous instance (name it to audit it): {line!r}")
        elif m := DECL.match(line):
            out.append(".".join(stack + [m.group(1)]))
    return out


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    decls = []
    for rel in MODULES:
        decls += declarations((root / rel).read_text(encoding="utf-8"))
    src = "".join(f"import {i}\n" for i in IMPORTS) + "".join(
        f"#print axioms {d}\n" for d in decls)
    with tempfile.TemporaryDirectory() as tmp:
        f = Path(tmp) / "AuditA3.lean"
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
    missing = [d for d in decls if d not in seen]
    bad = []
    for name, axioms in found:
        used = {a.strip() for a in axioms.replace("\n", " ").split(",") if a.strip()}
        if not used <= ALLOWED:
            bad.append((name, sorted(used - ALLOWED)))
    if missing or bad:
        print(out)
        print(f"missing={missing} forbidden={bad}", file=sys.stderr)
        return 1
    print(f"A3 axiom audit PASS: {len(decls)} declarations, "
          f"{len(found)} with allowlisted axioms, {len(clean)} axiom-free")
    return 0


if __name__ == "__main__":
    sys.exit(main())
