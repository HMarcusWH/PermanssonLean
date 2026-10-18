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
import shutil
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
    "wrong_terminal_horizon": re.compile(
        r"Tactic `decide` proved that the proposition[\s\S]*?is false|unsolved goals[\s\S]*?⊢ False"),
    "reset_before_action": re.compile(
        r"Tactic `decide` proved that the proposition[\s\S]*?is false|unsolved goals[\s\S]*?⊢ False"),
    "omitted_minimizing_start": re.compile(
        r"Tactic `decide` proved that the proposition[\s\S]*?is false|unsolved goals[\s\S]*?⊢ False"),
    "corrupt_denominator": re.compile(
        r"Tactic `decide` proved that the proposition[\s\S]*?is false|unsolved goals[\s\S]*?⊢ False"),
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


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def archive_previous_run(scratch: Path) -> str | None:
    """Retain prior measured evidence before replacing any current diagnostics."""
    previous = scratch / "receipt.json"
    if not previous.exists():
        return None
    destination = scratch / "history" / f"{time.time_ns()}-{sha256(previous)[:12]}"
    destination.mkdir(parents=True)
    for path in scratch.iterdir():
        if path.is_file():
            shutil.copy2(path, destination / path.name)
    return str(destination.relative_to(ROOT))


def changed_files(snapshot: dict[str, str]) -> list[str]:
    return [name for name, digest in snapshot.items()
            if not (ROOT / name).is_file() or sha256(ROOT / name) != digest]


def mutation_sources(sources: dict[str, str]) -> dict[str, str]:
    """Each adversary changes a mathematical obligation, never its environment."""
    tests = {
        "corrupt_terminal_literal": replace_once(
            sources["ExactTerminalTables"], "![0, 1, 0, 1", "![0, 2, 0, 1"),
        "wrong_world_probability": replace_once(
            sources["InterventionNumericalBridge"],
            "∂coin (pRep y.2 a)", "∂coin (pRep (!y.2) a)"),
        "new_world_learning": replace_once(
            sources["InterventionNumericalBridge"],
            "InterventionNumerics.next (learnerFlag m) u y a",
            "InterventionNumerics.next (learnerFlag m) u (y.1,x) a"),
        "swapped_update_protocol": replace_once(
            sources["InterventionNumericalBridge"],
            "| false, true => (Jupdate m).intervention.apply",
            "| false, true => (Jaction m).intervention.apply"),
        # Actual original time-three property, falsely labeled by its time-two row.
        "wrong_terminal_horizon": """import PermanssonResearch.X1.ExactMargins
namespace PermanssonResearch.X1
open PermanssonLean PermanssonLean.RegimeSpecification
set_option autoImplicit false
example : baselinePropertyValue property (protocolModel .equilibrium false false) ((0,0),true) =
    (InterventionNumerics.table false false false 2 ((0,0),true) : ℝ) := by
  rw [original_property_eq_table]
  have offByOne :
      InterventionNumerics.table false false false 3 ((0,0),true) =
        InterventionNumerics.table false false false 2 ((0,0),true) := by
    norm_num [InterventionNumerics.table, InterventionNumerics.tableData,
      InterventionNumerics.stateIndex]
  exact congrArg (fun q : ℚ => (q : ℝ)) offByOne
end PermanssonResearch.X1
""",
        # A denominator change in a well-typed literal for the actual one-step law.
        "corrupt_denominator": """import PermanssonResearch.X1.ExactMargins
namespace PermanssonResearch.X1
set_option autoImplicit false
example : kernelTerminal (protocolModel .equilibrium false false).inducedKernel 1 ((0,0),false) =
    ENNReal.ofReal ((1/5 : ℚ) : ℝ) := by
  rw [kernelTerminal_eq_rational]
  change ENNReal.ofReal (InterventionNumerics.terminal false false false 1 ((0,0),false) : ℝ) = _
  have tableBridge :
      InterventionNumerics.terminal false false false 1 ((0,0),false) =
        InterventionNumerics.table false false false 1 ((0,0),false) := by
    simpa using (InterventionNumerics.table_eq_terminal false false false 1 ((0,0),false)).symm
  have corruptedLiteral :
      InterventionNumerics.table false false false 1 ((0,0),false) = (1/5 : ℚ) := by
    norm_num [InterventionNumerics.table, InterventionNumerics.tableData,
      InterventionNumerics.stateIndex]
  exact congrArg (fun q : ℚ => ENNReal.ofReal (q : ℝ)) (tableBridge.trans corruptedLiteral)
end PermanssonResearch.X1
""",
        # The actual typed Jupdate atom uses the old memory for this action.
        # The false candidate instead reads the already-reset memory (1,1).
        "reset_before_action": """import PermanssonResearch.X1.ExactMargins
open MeasureTheory ProbabilityTheory
namespace PermanssonResearch.X1
set_option autoImplicit false
example :
    (protocolModel .learner false true).inducedKernel ((0,0),true) {((1,1),true)} =
      ENNReal.ofReal
        (InterventionNumerics.entry true false true ((1,1),true) ((1,1),true) : ℝ) := by
  rw [protocol_atom_eq]
  have wrongOrder :
      InterventionNumerics.entry true false true ((0,0),true) ((1,1),true) =
        InterventionNumerics.entry true false true ((1,1),true) ((1,1),true) := by
    norm_num [InterventionNumerics.entry, InterventionNumerics.rates,
      InterventionNumerics.next, OccupationNumerics.rates, learnerExtract,
      Fintype.sum_prod_type, sum_bool, boolMass, pRep, indicator]
  exact congrArg (fun q : ℚ => ENNReal.ofReal (q : ℝ)) wrongOrder
end PermanssonResearch.X1
""",
        # An altered domain must still cover the original predeclared starts.
        # Removing the unique learner/action attainer makes that obligation false.
        "omitted_minimizing_start": """import PermanssonResearch.X1.ExactMargins
namespace PermanssonResearch.X1
set_option autoImplicit false
def incompleteStarts : Set Y :=
  {y | y ∈ comparisonStarts ∧ y ≠ attainingStart true .action}
example : ∀ y : Y, y ∈ comparisonStarts → y ∈ incompleteStarts := by
  have missingStart : attainingStart true .action ∈ incompleteStarts := by
    simp [incompleteStarts]
  exact False.elim (missingStart.2 rfl)
end PermanssonResearch.X1
""",
    }
    assert set(tests) == set(EXPECTED_PROOF_FAILURES)
    return tests


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
    tests = mutation_sources(sources)
    previous_archive = archive_previous_run(scratch)
    receipt: dict[str, object] = {
        "receipt_version": 2,
        "driver_sha256": sha256(Path(__file__)),
        "verification_sha256": {
            path.relative_to(ROOT).as_posix(): sha256(path)
            for path in (Path(__file__).resolve(),
                         Path(__file__).resolve().with_name("test_paper_x1_lean_closure.py"))
        },
        "previous_receipt_archive": previous_archive,
        "compiler_command": command,
        "source_sha256": {
            f"PermanssonResearch/X1/{name}.lean": hashlib.sha256(
                (ROOT / f"PermanssonResearch/X1/{name}.lean").read_bytes()).hexdigest()
            for name in MODULES
        },
        "positive_controls": {}, "compiled_artifacts": {},
        "mutations": {}, "axiom_audit": {},
        "status": "RUNNING",
    }
    receipt_path = scratch / "receipt.json"
    receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    passed = True
    # Rebuild the actual original module paths, in dependency order. Each input
    # is byte-identical to its saved control, and its new artifact is hash-bound.
    # Merely importing an old .olean is never a positive control for current text.
    for name, source in sources.items():
        print("Checking positive control", name, flush=True)
        control = scratch / f"positive_{name}.lean"
        control.write_bytes((ROOT / f"PermanssonResearch/X1/{name}.lean").read_bytes())
        source_path = Path(f"PermanssonResearch/X1/{name}.lean")
        artifact_relative = f".lake/build/lib/lean/PermanssonResearch/X1/{name}.olean"
        artifact = ROOT / artifact_relative
        artifact.parent.mkdir(parents=True, exist_ok=True)
        started = time.monotonic()
        try:
            run = subprocess.run(command + ["-o", str(artifact), str(source_path)], cwd=ROOT, capture_output=True,
                                 text=True, encoding="utf-8", timeout=args.timeout)
            output = run.stdout + run.stderr
            expected_hash = receipt["source_sha256"][str(source_path).replace("\\", "/")]
            ok = (run.returncode == 0 and
                  not re.search(r"\berror(?:\([^)]*\))?:|declaration uses .sorry.", output) and
                  artifact.is_file() and sha256(control) == expected_hash and
                  sha256(ROOT / source_path) == expected_hash)
            result = {"status": "PASS" if ok else "FAIL", "returncode": run.returncode,
                      "elapsed": time.monotonic()-started,
                      "control_sha256": sha256(control), "input_source": str(source_path),
                      "recompiled_original_artifact": artifact_relative}
            if ok:
                receipt["compiled_artifacts"][artifact_relative] = sha256(artifact)
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
        changed = (changed_files(receipt["source_sha256"]) +
                   changed_files(receipt["verification_sha256"]) +
                   changed_files(receipt["compiled_artifacts"]))
        if changed:
            receipt.update(status="INVALID_ARTIFACT", changed_files=changed)
            receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
            return 1
        print("Checking", label, flush=True)
        path = scratch / f"{label}.lean"
        path.write_text(source, encoding="utf-8", newline="\n")
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
    except OSError as exc:
        output, ok = str(exc), False
        receipt["axiom_audit"] = {"status": "INVALID_ENVIRONMENT", "declarations": len(names)}
    (scratch / "axiom_audit.out").write_text(output, encoding="utf-8")
    passed &= ok
    changed = (changed_files(receipt["source_sha256"]) +
               changed_files(receipt["verification_sha256"]) +
               changed_files(receipt["compiled_artifacts"]))
    receipt["changed_files"] = changed
    receipt["status"] = "INVALID_ARTIFACT" if changed else ("PASS" if passed else "FAIL")
    passed &= not changed
    receipt_path.write_text(json.dumps(receipt, indent=2), encoding="utf-8")
    print(json.dumps(receipt, indent=2), flush=True)
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
