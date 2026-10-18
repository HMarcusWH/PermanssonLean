"""Kernel-checked negative tests and transitive axiom audit for exact X1 closure.

Build the four X1 closure modules first. By default this uses ``lake env lean``;
``--lean PATH`` uses an explicitly supplied pinned compiler and the caller's
LEAN_PATH. Scratch sources, diagnostics, and the receipt stay under .lake.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import time
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
MODULES = [
    "InterventionNumerics",
    "InterventionNumericalBridge",
    "ExactTerminalTables",
    "ExactMargins",
]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
INVALID_DIAGNOSTICS = re.compile(
    r"unknown module prefix|object file .* does not exist|no such file|"
    r"failed to (?:load|import|synthesize)|unknown (?:identifier|constant|tactic|namespace|option)|"
    r"unexpected (?:token|identifier|end|syntax)|unterminated|parse error|"
    r"expected (?:token|command|identifier|term|['\"`])|"
    r"invalid (?:header|field|syntax|import)|maximum (?:recursion|number of heartbeats)|"
    r"(?:time limit|timeout|out of memory|allocation failed|stack overflow)|"
    r"application type mismatch|function expected|could not (?:read|load|open).*file",
    re.IGNORECASE,
)
EXPECTED_PROOF_FAILURES = {
    "corrupt_terminal_literal": re.compile(
        r"Tactic `decide` proved that the proposition[\s\S]*?is false"),
    "wrong_world_probability": re.compile(r"Tactic `change` failed|'change' tactic failed"),
    "new_world_learning": re.compile(
        r"Tactic `change` failed|'change' tactic failed|Tactic `rfl` failed|'rfl' tactic failed|unsolved goals"),
    "swapped_update_protocol": re.compile(r"Tactic `rfl` failed|'rfl' tactic failed|unsolved goals"),
}
DECL = re.compile(
    r"(?:@\[[^\]]*\]\s*)?(?:(?:noncomputable|protected)\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class)\s+([^\s:({\[]+)"
)


def declaration_names(text: str) -> list[str]:
    names, namespaces = [], []
    for line in text.splitlines():
        if line.startswith("namespace "):
            namespaces.append(line.split()[1])
        elif line.startswith("end ") and namespaces:
            assert line.split()[1] == namespaces[-1]
            namespaces.pop()
        elif match := DECL.match(line):
            names.append(".".join(namespaces + [match.group(1)]))
    return names


def replace_once(text: str, old: str, new: str) -> str:
    assert text.count(old) >= 1, old
    return text.replace(old, new, 1)


def classify_mutation(label: str, returncode: int, output: str) -> dict[str, object]:
    """An unavailable environment or malformed source is never a semantic rejection."""
    invalid = sorted(set(match.group(0) for match in INVALID_DIAGNOSTICS.finditer(output)))
    expected = EXPECTED_PROOF_FAILURES[label].search(output)
    has_error = re.search(r"\berror(?:\([^)]*\))?:", output) is not None
    if invalid:
        status = "INVALID_TEST"
    elif returncode != 0 and has_error and expected:
        status = "REJECTED"
    elif returncode == 0:
        status = "ACCEPTED_MUTATION"
    else:
        status = "UNEXPECTED_DIAGNOSTIC"
    return {"status": status, "returncode": returncode,
            "expected_proof_failure": expected.group(0) if expected else None,
            "invalid_diagnostics": invalid}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default=os.environ.get("PERMANSSON_X1_LEAN"),
                        help="Pinned lean executable; preserve the caller's LEAN_PATH")
    parser.add_argument("--timeout", type=int, default=600)
    args = parser.parse_args()
    command = [args.lean] if args.lean else ["lake", "env", "lean"]
    scratch = ROOT / ".lake/x1-paper-closure"
    scratch.mkdir(parents=True, exist_ok=True)
    sources = {
        name: (ROOT / f"PermanssonResearch/X1/{name}.lean").read_text(encoding="utf-8")
        for name in MODULES
    }
    tests = {
        "corrupt_terminal_literal": replace_once(
            sources["ExactTerminalTables"], "![0, 1, 0, 1", "![0, 2, 0, 1"
        ),
        "wrong_world_probability": replace_once(
            sources["InterventionNumericalBridge"],
            "∂coin (pRep y.2 a)",
            "∂coin (pRep (!y.2) a)",
        ),
        "new_world_learning": replace_once(
            sources["InterventionNumericalBridge"],
            "InterventionNumerics.next (learnerFlag m) u y a",
            "InterventionNumerics.next (learnerFlag m) u (y.1,x) a",
        ),
        "swapped_update_protocol": replace_once(
            sources["InterventionNumericalBridge"],
            "| false, true => (Jupdate m).intervention.apply",
            "| false, true => (Jaction m).intervention.apply",
        ),
    }
    receipt: dict[str, object] = {
        "compiler_command": command,
        "source_sha256": {
            f"PermanssonResearch/X1/{name}.lean": hashlib.sha256(
                (ROOT / f"PermanssonResearch/X1/{name}.lean").read_bytes()).hexdigest()
            for name in MODULES
        },
        "positive_controls": {}, "mutations": {}, "axiom_audit": {},
        "status": "RUNNING",
    }
    receipt_path = scratch / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    passed = True
    # A negative result has evidential value only after these exact unmodified
    # sources elaborate in the same environment. Full Research CI builds their
    # imported artifacts first; these controls additionally check current text.
    for name, source in sources.items():
        print("Checking positive control", name, flush=True)
        control = scratch / f"positive_{name}.lean"
        control.write_bytes((ROOT / f"PermanssonResearch/X1/{name}.lean").read_bytes())
        started = time.monotonic()
        try:
            run = subprocess.run(command + [str(control)], cwd=ROOT, capture_output=True,
                                 text=True, encoding="utf-8", timeout=args.timeout)
            output = run.stdout + run.stderr
            ok = run.returncode == 0 and not re.search(r"\berror(?:\([^)]*\))?:", output)
            result = {"status": "PASS" if ok else "FAIL", "returncode": run.returncode,
                      "elapsed": time.monotonic()-started,
                      "control_sha256": hashlib.sha256(control.read_bytes()).hexdigest()}
        except subprocess.TimeoutExpired as exc:
            output, ok = str(exc), False
            result = {"status": "TIMEOUT", "elapsed": time.monotonic()-started}
        except OSError as exc:
            output, ok = str(exc), False
            result = {"status": "INVALID_ENVIRONMENT", "elapsed": time.monotonic()-started}
        (scratch / f"positive_{name}.out").write_text(output, encoding="utf-8")
        receipt["positive_controls"][name] = result
        passed &= ok
        receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
        print(name, json.dumps(result), flush=True)
    if not passed:
        receipt["status"] = "POSITIVE_CONTROL_FAILED"
        receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
        return 1

    for label, source in tests.items():
        print("Checking", label, flush=True)
        path = scratch / f"{label}.lean"
        path.write_text(source, encoding="utf-8")
        started = time.monotonic()
        try:
            run = subprocess.run(command + [str(path)], cwd=ROOT, capture_output=True,
                                 text=True, encoding="utf-8", timeout=args.timeout)
            output = run.stdout + run.stderr
            result = classify_mutation(label, run.returncode, output)
            result.update(elapsed=time.monotonic()-started,
                          mutation_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
            rejected = result["status"] == "REJECTED"
        except subprocess.TimeoutExpired as exc:
            output = str(exc)
            result = {"status": "TIMEOUT", "elapsed": time.monotonic()-started}
            rejected = False
        except OSError as exc:
            output, rejected = str(exc), False
            result = {"status": "INVALID_ENVIRONMENT", "elapsed": time.monotonic()-started}
        (scratch / f"{label}.out").write_text(output, encoding="utf-8")
        receipt["mutations"][label] = result
        receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
        passed &= rejected
        print(label, json.dumps(result), flush=True)

    names = [name for source in sources.values() for name in declaration_names(source)]
    audit = scratch / "axiom_audit.lean"
    print("Checking transitive axioms", flush=True)
    audit.write_text("import PermanssonResearch.X1.ExactMargins\n" + "".join(
        f"#print axioms {name}\n" for name in names), encoding="utf-8")
    try:
        run = subprocess.run(command + [str(audit)], cwd=ROOT, capture_output=True,
                             text=True, encoding="utf-8", timeout=args.timeout)
        output = run.stdout + run.stderr
        found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output, re.S)
        clean = re.findall(r"'([^']+)' does not depend on any axioms", output)
        seen = {name for name, _ in found} | set(clean)
        missing = sorted(set(names) - seen)
        forbidden = {
            name: sorted({a.strip() for a in axioms.replace("\n", " ").split(",")
                          if a.strip()} - ALLOWED)
            for name, axioms in found
        }
        forbidden = {name: used for name, used in forbidden.items() if used}
        ok = run.returncode == 0 and not missing and not forbidden
        receipt["axiom_audit"] = {"status": "PASS" if ok else "FAIL",
            "declarations": len(names), "returncode": run.returncode,
            "missing": missing, "forbidden": forbidden}
    except subprocess.TimeoutExpired as exc:
        output, ok = str(exc), False
        receipt["axiom_audit"] = {"status": "TIMEOUT", "declarations": len(names)}
    (scratch / "axiom_audit.out").write_text(output, encoding="utf-8")
    passed &= ok
    receipt["status"] = "PASS" if passed else "FAIL"
    receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(json.dumps(receipt, indent=2), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
