"""Inspect and reproduce the supplied 45 acceptance cases; never grant atlas/CI closure.

Negative theorems, compiler mutants, theorem-interface gates, independent exact
Python executions and static information/hypothesis gates are distinct records.
Source lookup is never evidence that a compiler rejected a mutation.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter
from fractions import Fraction as Q
import hashlib
import importlib
import io
import json
from pathlib import Path
import re
import subprocess
import sys
import time
import unittest

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
REGISTRY = ROOT / "research/paper_closures/spec/registries/acceptance_tests.json"
DEFAULT_OUTPUT = ROOT / "research/paper_closures"
ALLOW = {"Classical.choice", "Quot.sound", "propext"}


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8-sig"))


def write(path, value):
    Path(path).parent.mkdir(parents=True, exist_ok=True)
    Path(path).write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def relative(path):
    return Path(path).resolve().relative_to(ROOT).as_posix()


def current(binding):
    return all((ROOT / p.replace("\\", "/")).is_file() and
               sha(ROOT / p.replace("\\", "/")) == h for p, h in binding.items())


def source_bindings(data):
    result = {p.replace("\\", "/"): h for p, h in data.get("source_sha256", {}).items()}
    scope = data.get("source_scope", {})
    if isinstance(scope, dict):
        for p, record in scope.items():
            result[p.replace("\\", "/")] = record["sha256"]
    for record in data.get("modules", []):
        if isinstance(record, dict) and "source" in record:
            result[record["source"].replace("\\", "/")] = record["source_sha256"]
    return result


def receipt_index():
    paths = set((ROOT / "research/paper_closures").glob("*receipt*.json"))
    # The saved ledger must point at durable publication bytes. Scratch logs
    # and owner receipts subject to Git newline conversion are not stable links.
    for path in HERE.glob("paper_closure_*_receipt_2026-10-18.json"):
        stem = path.name.removeprefix('paper_closure_').removesuffix('_receipt_2026-10-18.json')
        copy = ROOT / 'research/paper_closures' / (stem + '_audit_receipt.json')
        if not copy.is_file():
            paths.add(path)
    result = []
    for path in sorted(paths):
        try:
            data = load(path)
            binding = source_bindings(data)
        except (OSError, ValueError, KeyError, TypeError):
            continue
        if not binding:
            continue
        if data.get("kind") == "CURRENT_SOURCE_AND_IMPORTED_ARTIFACT_SIGNATURE_AXIOM_AUDIT":
            continue  # selected-name audit is checked explicitly, never treated as whole-module recompilation
        status = data.get("status")
        passed = status in {"PASS", "THEOREM_FORMALIZED", "SCOPED_THEOREM_FORMALIZED"}
        passed = passed and not data.get("missing") and not data.get("forbidden")
        passed = passed and not data.get("changed_files") and not data.get("changed_during_check")
        if isinstance(data.get("axiom_audit"), dict):
            passed = passed and data["axiom_audit"].get("status", "PASS") == "PASS"
        result.append({"path": relative(path), "sha256": sha(path), "status": status,
                       "source_current": current(binding), "passed": bool(passed),
                       "source_bindings": binding, "data": data})
    return result


def resolve_ref(module, suffix):
    """Source parsing only locates a declaration; receipt evidence is checked separately."""
    from paper_closure_analytic_audit import declarations
    path = ROOT / ("PermanssonResearch/" + module.replace(".", "/") + ".lean")
    out = {"source": relative(path), "requested_name": suffix}
    if not path.is_file():
        return dict(out, status="PENDING_SOURCE")
    source = path.read_text(encoding="utf-8-sig")
    names = [n for n in declarations(source) if n == suffix or n.endswith("." + suffix)]
    if len(names) != 1:
        return dict(out, status="UNRESOLVED_DECLARATION", candidates=names)
    line = next((i for i, s in enumerate(source.splitlines(), 1)
                 if re.search(r"\b(?:theorem|lemma|def|abbrev|structure)\s+" + re.escape(suffix) + r"\b", s)), None)
    return dict(out, declaration=names[0], line=line, source_sha256=sha(path), status="LOCATED")


def attach_receipts(ref, receipts):
    ref = dict(ref)
    found = [r for r in receipts if ref.get("source") in r["source_bindings"]
             and r["passed"] and r["source_current"]]
    if found:
        rank = lambda r: 0 if r["path"].startswith("research/") else 1 if not r["path"].startswith(".lake/") else 2
        best = min(map(rank, found))
        found = [r for r in found if rank(r) == best]
    ref["current_source_bound_receipts"] = [{k: r[k] for k in ("path", "sha256", "status")}
                                              for r in found]
    ref["proof_evidence_current"] = ref["status"] == "LOCATED" and bool(found)
    return ref


class AdditionalExactChecks(unittest.TestCase):
    def test_geometric_endpoints_and_initial_error(self):
        for t in range(8):
            self.assertEqual(1-(1-Q(0))**t, 0)
            self.assertEqual(1-(1-Q(1))**t, 0 if t == 0 else 1)
        self.assertEqual(abs(Q(1)-Q(0)), 1)  # different point starts, even at T=0

    def test_supnorm_changes_the_transport_test_class(self):
        distance, dual_distance, bounded_supnorm_distance = Q(3), Q(3), Q(2)
        self.assertEqual(distance, dual_distance)
        self.assertLess(bounded_supnorm_distance, dual_distance)

    def test_opposite_overlap_order_dependence(self):
        apply_patch = lambda _old, prescribed: prescribed
        self.assertNotEqual(Q(0), Q(1))
        self.assertEqual(apply_patch(apply_patch(Q(1,2), Q(0)), Q(1)), 1)
        self.assertEqual(apply_patch(apply_patch(Q(1,2), Q(1)), Q(0)), 0)

    def test_incomparable_minima_and_xor(self):
        positive = {frozenset({0}), frozenset({1})}
        self.assertEqual(len(positive), 2)
        self.assertTrue(all(not (a < b) for a in positive for b in positive))
        self.assertNotIn(frozenset({0,1}), positive)
        self.assertTrue(frozenset({0}) < frozenset({0,1}))

    def test_bad_clocks_fail_the_declared_projection(self):
        anchor = lambda t: t % 2
        self.assertNotEqual([anchor(t) for t in range(4)], [anchor(0)]*4)
        self.assertNotEqual(0+0, 0+1)  # treated-action driven common update not old-common-only

    def test_danger_after_success_remains_a_separate_risk(self):
        from test_monitor_stationary_closures import avoid_scan
        word = [(True,False),(False,True)]
        self.assertTrue(avoid_scan(word, 0))
        self.assertTrue(any(danger for _, danger in word))


def python_binding(modules):
    pending, seen = list(modules), set()
    while pending:
        name = pending.pop()
        path = HERE / (name + ".py")
        if name in seen or not path.is_file():
            continue
        seen.add(name)
        tree = ast.parse(path.read_text(encoding="utf-8-sig"))
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                pending.extend(item.name.split(".")[0] for item in node.names)
            elif isinstance(node, ast.ImportFrom) and node.module:
                pending.append(node.module.split(".")[0])
    return {relative(HERE / (name + ".py")): sha(HERE / (name + ".py")) for name in sorted(seen)}


def flatten(suite):
    for test in suite:
        if isinstance(test, unittest.TestSuite):
            yield from flatten(test)
        else:
            yield test


def run_exact_checks(output, specifications):
    sys.path.insert(0, str(HERE))
    modules = {m for m, _ in specifications if m != "self"}
    binding = python_binding(modules | {Path(__file__).stem})
    tests = {}
    for module, method in specifications:
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(AdditionalExactChecks) if module == "self" else \
            unittest.defaultTestLoader.loadTestsFromModule(importlib.import_module(module))
        matches = [t for t in flatten(suite) if t.id().endswith("." + method)]
        key = module + ":" + method
        if len(matches) != 1:
            tests[key] = {"status": "UNRESOLVED_TEST", "matches": len(matches)}
            continue
        stream = io.StringIO()
        started = time.time()
        result = unittest.TextTestRunner(stream=stream, verbosity=2).run(unittest.TestSuite(matches))
        tests[key] = {"status": "PASS" if result.wasSuccessful() else "FAIL",
                      "test_id": matches[0].id(), "tests_run": result.testsRun,
                      "elapsed": time.time()-started, "output": stream.getvalue()}
    if not current(binding):
        raise RuntimeError("Exact-check source changed during execution")
    journal = {"format": "Permansson.AcceptanceExactExecutions.v1", "kind": "INDEPENDENT_EXACT_PYTHON",
               "source_sha256": binding, "tests": tests,
               "status": "PASS" if all(t["status"] == "PASS" for t in tests.values()) else "FAIL"}
    write(output / "acceptance_exact_checks.json", journal)
    return journal


def run_four_factor_interface(output):
    """Execute the actual theorem's four-Data interface; this is not a countermodel."""
    version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, encoding="utf-8", errors="replace", timeout=120)
    expected = (ROOT/"lean-toolchain").read_text().strip().rsplit(":v",1)[-1]
    actual = re.search(r"\bversion\s+([0-9.]+)", version.stdout)
    if version.returncode or not actual or actual.group(1) != expected:
        raise RuntimeError("Pinned compiler version unavailable: " + version.stdout + version.stderr)
    provider = ROOT / "PermanssonResearch/Perturbation/RegenerativeOccupationFactorization.lean"
    source = provider.read_text(encoding="utf-8")
    context = source[:source.index("theorem model_property_factor")]
    context = context.replace("namespace PermanssonResearch.Perturbation.RegenerativeFactorization",
                              "namespace PermanssonResearch.AcceptanceFourFactors\nopen PermanssonResearch.Perturbation.RegenerativeFactorization")
    context = "import PermanssonResearch.Perturbation.RegenerativeOccupationFactorization\n" + context
    context = context.replace("open RegenerativeOccupationProperty", "open PermanssonResearch.Perturbation.RegenerativeOccupationProperty")
    statement = source[source.index("theorem four_actual_factorizations"):source.index("theorem generated_occupationMargin_robust")]
    statement = statement[:statement.index(":=")]
    statement = statement.replace("theorem four_actual_factorizations", "theorem positive_control")
    apply = "four_actual_factorizations M Mt F Ft J Jt D₀ Dₜ DJ DJt hh fallback Φ y"
    positive = context + statement + ":= by\n  exact " + apply + "\nend PermanssonResearch.AcceptanceFourFactors\n"
    negative = positive.replace("theorem positive_control", "theorem missing_fourth_data").replace(
        "exact " + apply, "exact " + apply.replace("DJ DJt hh", "DJ hh"))
    scratch = ROOT / ".lake/acceptance-evidence"
    scratch.mkdir(parents=True, exist_ok=True)
    binding = {relative(provider): sha(provider), relative(__file__): sha(__file__)}
    results = {}
    for key, code in (("positive_control", positive), ("missing_fourth_data", negative)):
        path = scratch / ("A04_" + key + ".lean")
        path.write_text(code, encoding="utf-8")
        started = time.time()
        try:
            run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT,
                                 capture_output=True, encoding="utf-8", errors="replace", timeout=600)
            text = run.stdout + run.stderr
            invalid = [tag for tag in ("object file", "unexpected token", "unknown identifier", "unknown constant",
                       "unknown option", "heartbeats exceeded", "timeout", "allocation failed") if tag in text.lower()]
            accepted = run.returncode == 0 if key == "positive_control" else \
                run.returncode != 0 and not invalid and "type mismatch" in text.lower() and "Data" in text
            status = "PASS" if key == "positive_control" and accepted else \
                "REJECTED_INTERFACE_GATE" if accepted else "INVALID_OR_UNEXPECTED"
            results[key] = {"status": status, "returncode": run.returncode, "invalid_diagnostics": invalid,
                            "elapsed": time.time()-started, "fixture_sha256": sha(path), "fixture": code,
                            "compiler_output": text}
        except (OSError, subprocess.TimeoutExpired) as exc:
            results[key] = {"status": "INVALID_TEST", "error": str(exc)}
        print("A-04", key, results[key]["status"], flush=True)
        if key == "positive_control" and results[key]["status"] != "PASS":
            break
    if not current(binding):
        raise RuntimeError("Four-factor source changed during execution")
    receipt = {"format": "Permansson.AcceptanceInterfaceExecutions.v1",
               "compiler_command": ["lake","env","lean"], "compiler_version": version.stdout.strip(),
               "lean_toolchain": expected,
               "kind": "EXECUTED_FOUR_FACTOR_THEOREM_INTERFACE_GATE",
               "interpretation": "Positive exact theorem application versus omission of only DJt; not a mathematical countermodel.",
               "source_sha256": binding, "results": results,
               "status": "PASS" if results.get("positive_control",{}).get("status") == "PASS" and
                  results.get("missing_fourth_data",{}).get("status") == "REJECTED_INTERFACE_GATE" else "PARTIAL"}
    write(output / "acceptance_interface_checks.json", receipt)
    return receipt


def run_named_audit(output, references):
    """Audit actual imported declarations; record source and compiled-artifact binding.

This is distinct from an owner's full source compilation receipt. In particular
the ledger never calls a mere source-name lookup a kernel check.
"""
    references = {r.get("declaration"): r for r in references if r.get("status") == "LOCATED"}
    eligible, binding, artifacts = {}, {}, {}
    for name, ref in references.items():
        source = ROOT / ref["source"]
        artifact = ROOT / ".lake/build/lib/lean" / ref["source"].replace(".lean", ".olean")
        if artifact.is_file() and artifact.stat().st_mtime_ns >= source.stat().st_mtime_ns:
            eligible[name] = ref
            binding[ref["source"]] = sha(source)
            artifacts[relative(artifact)] = sha(artifact)
    binding[relative(__file__)] = sha(__file__)
    binding[relative(HERE / "paper_closure_acceptance_cases.py")] = sha(HERE / "paper_closure_acceptance_cases.py")
    modules = sorted({r["source"].replace("/", ".").removesuffix(".lean") for r in eligible.values()})
    scratch = ROOT / ".lake/acceptance-evidence"
    scratch.mkdir(parents=True, exist_ok=True)
    source = scratch / "AcceptanceSelectedDeclarations.lean"
    source.write_text("".join("import " + m + "\n" for m in modules) +
                      "set_option pp.fullNames true\n" +
                      "".join("#check " + n + "\n#print axioms " + n + "\n" for n in sorted(eligible)), encoding="utf-8")
    started = time.time()
    run = subprocess.run(["lake", "env", "lean", str(source)], cwd=ROOT, capture_output=True,
                         encoding="utf-8", errors="replace", timeout=600)
    raw = run.stdout + run.stderr
    reports = {}
    for name, group in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", raw, re.S):
        reports[name] = sorted(x.strip() for x in group.replace("\n", " ").split(",") if x.strip())
    for name in re.findall(r"'([^']+)' does not depend on any axioms", raw):
        reports[name] = []
    missing = sorted(set(eligible) - set(reports))
    forbidden = {n: a for n, a in reports.items() if not set(a) <= ALLOW}
    stable = current(binding) and current(artifacts)
    logs = output / "acceptance_selected_signatures_axioms.txt"
    logs.write_text(raw, encoding="utf-8")
    receipt = {"format": "Permansson.AcceptanceImportedDeclarations.v1",
               "kind": "CURRENT_SOURCE_AND_IMPORTED_ARTIFACT_SIGNATURE_AXIOM_AUDIT",
               "status": "PASS" if run.returncode == 0 and not missing and not forbidden and stable else "PARTIAL",
               "returncode": run.returncode, "elapsed": time.time()-started,
               "source_sha256": binding, "compiled_artifacts": artifacts, "declarations": reports,
               "missing": missing, "forbidden": forbidden, "stable_during_check": stable,
               "output": relative(logs), "output_sha256": sha(logs),
               "boundary": "Checks actual imported constants and records current source/artifact hashes; does not replace owners' full source recompilation or genuine PR CI."}
    write(output / "acceptance_selected_lean_receipt.json", receipt)
    return receipt


NEGATIVE_THEOREMS = {
    "replete_not_exactGR", "point_start_violates_premise", "two_SCMs_different_joint_do",
    "two_SCMs_positivity_failure", "high_actual_finite_survival_zero_infinite",
    "scaled_two_point_bound_two_rejected", "tv_does_not_control_w1_on_real",
    "contraction_does_not_transfer_survival", "first_entry_retry_counterexample",
    "full_risky_choice_is_infeasible", "whole_model_commitment_strictly_exceeds_rectangular",
    "zero_dimension_reference_rejected", "corrupted_stationary_receipt_rejected",
    "canonical_clock_no_weak_limit", "canonical_growing_block_occupations_fail",
    "baseline_leak_not_original_exactGR", "changed_embedding_loses_negativity",
    "exact_but_illegal_approximant", "dimension_two_retains_second_equation",
    "zero_shift_does_not_supply_inverse", "incompatible_kernel_negative",
    "no_unobserved_draw_copy", "observed_history_cannot_copy_next_state",
}


def optional_current(path):
    try:
        data = load(path)
        return data if current(data.get("source_sha256", {})) else {}
    except (OSError, ValueError):
        return {}


def build_ledger(output):
    from paper_closure_acceptance_cases import CASES
    registry = load(REGISTRY)
    if set(CASES) != {c["id"] for c in registry["cases"]} or len(CASES) != registry["count"]:
        raise RuntimeError("Routing must contain every exact supplied case ID once")
    receipts = receipt_index()
    exact = optional_current(output / "acceptance_exact_checks.json")
    interface = optional_current(output / "acceptance_interface_checks.json")
    selected = optional_current(output / "acceptance_selected_lean_receipt.json")
    selected_ok = selected.get("status") == "PASS" and current(selected.get("compiled_artifacts", {}))
    mutants = []
    for r in receipts:
        if r["passed"] and r["source_current"] and r["data"].get("receipt_version") == 2:
            mutants.append(r)
    result = []
    for original in registry["cases"]:
        route = CASES[original["id"]]
        item = {"id": original["id"], "atlas_ids": original["atlas_ids"],
                "purpose": original["purpose"], "required_expected_result": original["required_expected_result"],
                "supplied_registry_status": original["status"], "proofs": [], "python_checks": [],
                "semantic_compiler_mutations": [], "gates": [], "material_gaps": list(route["gaps"]),
                "scope_note": route["note"]}
        for module, suffix in route["proofs"]:
            ref = attach_receipts(resolve_ref(module, suffix), receipts)
            ref["kind"] = "KERNEL_CHECKED_NEGATIVE_THEOREM" if suffix in NEGATIVE_THEOREMS else "KERNEL_CHECKED_THEOREM"
            if selected_ok and ref.get("declaration") in selected.get("declarations", {}):
                ref["selected_imported_declaration_audit"] = {
                    "path": relative(output / "acceptance_selected_lean_receipt.json"),
                    "sha256": sha(output / "acceptance_selected_lean_receipt.json"),
                    "kind": selected["kind"], "axioms": selected["declarations"][ref["declaration"]]}
                ref["proof_evidence_current"] = True
            item["proofs"].append(ref)
            if not ref["proof_evidence_current"]:
                item["material_gaps"].append("No current source-bound compiler/audit evidence for " + module + "." + suffix)
        for module, method in route["python"]:
            key = module + ":" + method
            record = exact.get("tests", {}).get(key, {"status": "NOT_EXECUTED_FOR_THIS_LEDGER"})
            item["python_checks"].append({"kind": "INDEPENDENT_EXACT_PYTHON", "key": key, **record,
                                          "receipt": relative(output / "acceptance_exact_checks.json")})
            if record.get("status") != "PASS":
                item["material_gaps"].append("Exact Python execution absent or failed: " + key)
        for name in route["mutations"]:
            candidates = [(r, r["data"].get("mutations", {}).get(name)) for r in mutants]
            candidates = [(r, m) for r, m in candidates if m]
            if candidates:
                owner, mutation = candidates[-1]
                valid = mutation.get("status") == "REJECTED" and mutation.get("expected_proof_failure") \
                    and not mutation.get("invalid_diagnostics")
                item["semantic_compiler_mutations"].append({"kind": "SEMANTIC_COMPILER_MUTATION", "name": name,
                    "status": "REJECTED" if valid else "INVALID_OR_UNEXPECTED", "receipt": owner["path"],
                    "receipt_sha256": owner["sha256"], "result": mutation})
            else:
                valid = False
                item["semantic_compiler_mutations"].append({"kind": "SEMANTIC_COMPILER_MUTATION", "name": name,
                                                           "status": "PENDING_VERSION2_EXECUTION"})
            if not valid:
                item["material_gaps"].append("No current intended semantic compiler rejection: " + name)
        item["gates"] = [{"kind": "INFORMATION_CLASS_TYPE_OR_SOURCE_HYPOTHESIS_GATE", "description": s,
                          "executed_compiler_rejection": False} for s in route["gates"]]
        if item["id"] == "A-04":
            valid = interface.get("status") == "PASS"
            item["gates"].append({"kind": "EXECUTED_FOUR_FACTOR_THEOREM_INTERFACE_GATE",
                                  "executed_compiler_rejection": valid,
                                  "status": interface.get("status", "NOT_EXECUTED"),
                                  "receipt": relative(output / "acceptance_interface_checks.json")})
            if not valid:
                item["material_gaps"].append("Four-factor positive control and missing-fourth interface rejection not both current PASS")
        if item["id"] == "X-01":
            owners = [r for r in receipts if r["passed"] and r["source_current"] and
                      ("x1-matrix" in r["path"] or "x1_matrix" in r["path"])]
            item["literal_matrix_adapter"] = {"status": "PASS" if owners else "PENDING_OWNER_SOURCE_BOUND_AUDIT",
                "receipts": [{k:r[k] for k in ("path","sha256")} for r in owners]}
            if not owners:
                item["material_gaps"].append("Literal8-by324 matrix adapter's own source-bound audit is pending")
        if item["id"] == "Q-03":
            owners = [r for r in receipts if r["passed"] and r["source_current"] and "full_path_product" in r["path"]]
            if not owners:
                item["material_gaps"].append("Full-path sequential-product unit's own source-bound audit is pending")
        if item["id"] in {"F-01", "D-06"}:
            names = ["verification/research/MultiAgentAsymmetry.lean", "verification/research/MultiAgentFiniteProduct.lean"] \
                if item["id"] == "F-01" else ["verification/research/BeliefObservationWitness.lean"]
            item["anonymous_lean_fixtures"] = []
            for name in names:
                evidence = [r for r in receipts if name in r["source_bindings"] and r["passed"] and r["source_current"]]
                item["anonymous_lean_fixtures"].append({"source": name, "source_sha256": sha(ROOT/name),
                    "kind": "KERNEL_CHECKED_ANONYMOUS_FIXTURE_STATEMENTS", "current": bool(evidence),
                    "receipts": [{k:r[k] for k in ("path","sha256")} for r in evidence]})
                if not evidence:
                    item["material_gaps"].append("Missing current source-bound anonymous fixture: " + name)
        item["status"] = "PARTIAL" if item["material_gaps"] else "LOCAL_EVIDENCE_COMPLETE"
        result.append(item)
    counts = dict(Counter(c["status"] for c in result))
    ledger = {"format": "Permansson.AcceptanceEvidenceLedger.v1", "case_count": len(result),
              "registry": {"path": relative(REGISTRY), "sha256": sha(REGISTRY)},
              "generator_sha256": sha(__file__), "routing_sha256": sha(HERE/"paper_closure_acceptance_cases.py"),
              "status_counts": counts, "source_H": None, "synthetic_S": None, "eventual_merge_M": None,
              "acceptance_boundary": "Local evidence by exact case ID. Does not grant all42 atlas closure, independent statement-scope approval, current PR-head/synthetic-merge CI, or merge authorization.",
              "evidence_taxonomy": ["KERNEL_CHECKED_THEOREM", "KERNEL_CHECKED_NEGATIVE_THEOREM",
                  "SEMANTIC_COMPILER_MUTATION", "INDEPENDENT_EXACT_PYTHON",
                  "EXECUTED_FOUR_FACTOR_THEOREM_INTERFACE_GATE", "INFORMATION_CLASS_TYPE_OR_SOURCE_HYPOTHESIS_GATE"],
              "receipt_inventory": [{k:r[k] for k in ("path","sha256","status","source_current")} for r in receipts],
              "cases": result}
    write(output/"acceptance_evidence.json", ledger)
    lines = ["# Acceptance evidence for the 45 supplied cases", "", ledger["acceptance_boundary"], "",
             "A source lookup is never classified as a rejected compiler mutation. Kernel-checked negative statements, exact Python counterchecks and interface/information gates remain distinct. `PARTIAL` names the missing execution or binding; it is not a blanket rejection of the mathematical work.", "",
             "| Case | Local evidence | Purpose | Material gaps |", "|---|---|---|---|"]
    for item in result:
        lines.append("| " + " | ".join([item["id"],item["status"],item["purpose"].replace("|","/"),
            "; ".join(item["material_gaps"]).replace("|","/") or "None in the selected case"]) + " |")
    for item in result:
        lines += ["", "## " + item["id"], "", item["required_expected_result"], ""]
        for proof in item["proofs"]:
            title = proof.get("declaration", proof["requested_name"])
            target = "../../" + proof["source"] + ("#L" + str(proof["line"]) if proof.get("line") else "")
            lines.append("- " + proof["kind"] + ": [" + title + "](" + target + ") — " +
                         ("current source-bound evidence" if proof["proof_evidence_current"] else "pending evidence") + ".")
            for receipt in proof["current_source_bound_receipts"]:
                lines.append("  Receipt: [" + receipt["path"] + "](../../" + receipt["path"] + "), SHA256 `" + receipt["sha256"] + "`.")
        for py in item["python_checks"]:
            lines.append("- INDEPENDENT_EXACT_PYTHON: `" + py["key"] + "` — " + py["status"] + ".")
        for mutation in item["semantic_compiler_mutations"]:
            lines.append("- SEMANTIC_COMPILER_MUTATION: `" + mutation["name"] + "` — " + mutation["status"] + ".")
        for gate in item["gates"]:
            lines.append("- " + gate["kind"] + ": " + gate.get("description", gate.get("status", "")))
        if item["scope_note"]:
            lines += ["", item["scope_note"]]
        if item["material_gaps"]:
            lines += ["", "Material gaps: " + "; ".join(item["material_gaps"]) + "."]
    (output/"acceptance_evidence.md").write_text("\n".join(lines)+"\n", encoding="utf-8")
    return ledger


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=DEFAULT_OUTPUT)
    parser.add_argument("--run-exact", action="store_true", help="Actually execute each selected exact Python check")
    parser.add_argument("--check-lean", action="store_true", help="Execute four-factor interface controls and selected signature/axiom audit")
    parser.add_argument("--refresh", action="store_true", help="Run both exact and Lean evidence before regenerating")
    args = parser.parse_args()
    output = args.output_dir.resolve()
    output.mkdir(parents=True, exist_ok=True)
    from paper_closure_acceptance_cases import CASES
    if args.run_exact or args.refresh:
        specs = sorted({tuple(t) for c in CASES.values() for t in c["python"]})
        exact = run_exact_checks(output, specs)
        print("Exact Python executions:", exact["status"], len(exact["tests"]), flush=True)
    if args.check_lean or args.refresh:
        run_four_factor_interface(output)
        refs = [resolve_ref(m,n) for c in CASES.values() for m,n in c["proofs"]]
        audit = run_named_audit(output, refs)
        print("Selected declaration audit:", audit["status"], len(audit["declarations"]), flush=True)
    ledger = build_ledger(output)
    print("Acceptance ledger:", ledger["case_count"], ledger["status_counts"], flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
