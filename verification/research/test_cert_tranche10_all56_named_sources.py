"""Complete selected-name execution across the frozen 56-case ledger.

The 139 case-owned route occurrences deduplicate to 136 compiler declarations.
This checks availability, signatures, source binding and trusted axioms only;
it does not claim every literal criterion or semantic control is discharged,
and it never promotes an independent certification decision.
"""
from __future__ import annotations

from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import unittest

from verification.research.paper_closure_acceptance_cases import CASES
from verification.research.paper_closure_analytic_audit import declarations
from verification.research.test_cert_tranche3_source_bound_replay import parse_axiom_receipt
from verification.research.test_cert_q05_whole_path_addendum import (
    require_no_proof_placeholders_or_axiom_commands,
)

ROOT = Path(__file__).resolve().parents[2]
SPEC_PATH = ROOT / "verification/research/certification_addenda_20261120/Tranche10_All56_Named_Source_Spec.json"
FROZEN_MATRIX_SHA256 = "6a5af6129dffebb26e0fd92bb20800d2d289a6d0cc115caccd179bb541df8e4a"
FROZEN_COUNTS = {
    "original_45/PENDING": 15,
    "original_45/PARTIAL_SCOPE": 30,
    "later_11/SOURCE_PRESENT_REVIEW_PENDING": 11,
}


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def specification() -> dict:
    return json.loads(SPEC_PATH.read_text(encoding="utf-8"))


def frozen_hashes(spec: dict) -> dict:
    return {path: sha256((ROOT / path).read_bytes())
            for path in spec["frozen_source_sha256"]}


def provider_artifacts(spec: dict) -> dict:
    artifacts = {}
    for module in spec["import_modules"]:
        path = ROOT / ".lake/build/lib/lean" / (module.replace(".", "/") + ".olean")
        if not path.is_file():
            raise AssertionError("Build the declared provider module before replay: " + module)
        artifacts[str(path.relative_to(ROOT))] = sha256(path.read_bytes())
    return artifacts


class Tranche10All56NamedSources(unittest.TestCase):
    def test_frozen_56_rows_routes_pins_and_exact_declaration_ownership(self):
        spec = specification()
        self.assertEqual(spec["acceptance_changes"], 0)
        self.assertEqual(spec["case_count"], 56)
        self.assertEqual(spec["semantic_controls_in_this_named_source_probe"], 0)
        self.assertEqual(spec["frozen_matrix_sha256"], FROZEN_MATRIX_SHA256)
        raw = spec["frozen_matrix_json"].encode("utf-8")
        self.assertEqual(sha256(raw), FROZEN_MATRIX_SHA256)
        frozen = json.loads(raw)
        frozen_by_key = {row["family"] + "/" + row["id"]: row for row in frozen}
        self.assertEqual(len(frozen_by_key), 56)
        self.assertEqual(dict(Counter(row["family"] + "/" + row["status"]
                                      for row in frozen)), FROZEN_COUNTS)
        self.assertEqual(spec["frozen_counts"], FROZEN_COUNTS)
        self.assertEqual(frozen_hashes(spec), spec["frozen_source_sha256"])
        self.assertEqual((ROOT / "lean-toolchain").read_text().strip(),
                         spec["required_lean_toolchain"])
        self.assertEqual(spec["required_lean_toolchain"], "leanprover/lean4:v4.34.0")
        self.assertEqual(spec["axiom_allowlist"], ["Classical.choice", "Quot.sound", "propext"])
        registry = json.loads((ROOT / "research/paper_closures/spec/registries/acceptance_tests.json")
                              .read_text(encoding="utf-8"))
        criteria = {item["id"]: item for item in registry["cases"]}
        decisions = json.loads((ROOT / "research/paper_closures/post_merge_112/acceptance_decisions.json")
                               .read_text(encoding="utf-8"))
        historical = {row["case_id"]: row for row in decisions["cases"]}
        self.assertEqual([case["key"] for case in spec["cases"]], list(frozen_by_key))
        self.assertEqual(len(spec["cases"]), 56)
        provider_names = {}
        owners = {}
        modules = []
        route_counts = Counter()
        for case in spec["cases"]:
            key = case["key"]
            row = frozen_by_key[key]
            self.assertEqual((case["family"], case["id"], case["frozen_status"]),
                             (row["family"], row["id"], row["status"]))
            self.assertFalse(case["independent_acceptance_changed"])
            self.assertEqual(case["frozen_interpretation"], row["interpretation"])
            self.assertEqual(case["frozen_limitation"], row["limitation"])
            refs = case["named_routes"]
            self.assertTrue(refs, key)
            route_counts[case["family"]] += len(refs)
            self.assertEqual(case["expected_declarations"], [r["declaration"] for r in refs])
            if case["family"] == "original_45":
                self.assertEqual(case["literal_criterion"], criteria[case["id"]])
                self.assertEqual(case["historical_scope"], historical[case["id"]]["implemented_claim"])
                self.assertEqual(case["historical_objections"],
                                 historical[case["id"]]["remaining_obligations"])
                self.assertEqual(case["legacy_route"]["proofs"],
                                 [list(pair) for pair in CASES[case["id"]]["proofs"]])
                expected_routes = [("PermanssonResearch." + m, n)
                                   for m, n in CASES[case["id"]]["proofs"]]
                self.assertEqual([(r["module"], r["requested_suffix"]) for r in refs],
                                 expected_routes)
            else:
                self.assertEqual(case["family"], "later_11")
                expected_later = []
                for item in row["qualified_declarations"].split("; "):
                    name, location = item.split("@")
                    path, line = location.rsplit(":", 1)
                    expected_later.append((name, path, int(line)))
                self.assertEqual([(r["declaration"], r["source"], r["source_line"])
                                  for r in refs], expected_later)
            for ref in refs:
                name, source = ref["declaration"], ref["source"]
                self.assertEqual(source, ref["module"].replace(".", "/") + ".lean")
                self.assertEqual(ref["source_sha256"], spec["frozen_source_sha256"][source])
                if source not in provider_names:
                    provider_names[source] = declarations((ROOT / source).read_text(encoding="utf-8-sig"))
                self.assertIn(name, provider_names[source], (key, name))
                if ref["requested_suffix"] is not None:
                    suffix = ref["requested_suffix"]
                    self.assertEqual([n for n in provider_names[source]
                                      if n == suffix or n.endswith("." + suffix)], [name])
                if name not in owners:
                    owners[name] = {"declaration": name, "source": source,
                                    "source_sha256": ref["source_sha256"], "case_keys": []}
                self.assertEqual(owners[name]["source"], source)
                if key not in owners[name]["case_keys"]:
                    owners[name]["case_keys"].append(key)
                if ref["module"] not in modules:
                    modules.append(ref["module"])
        self.assertEqual(dict(route_counts), {"original_45": 104, "later_11": 35})
        self.assertEqual(spec["original_route_occurrences"], 104)
        self.assertEqual(spec["later_route_occurrences"], 35)
        self.assertEqual(spec["route_occurrences"], 139)
        self.assertEqual(spec["distinct_declarations"], 136)
        self.assertEqual(spec["provider_module_count"], 77)
        self.assertEqual(len(owners), 136)
        self.assertEqual(len(modules), 77)
        self.assertEqual(list(owners.values()), spec["declaration_ownership"])
        self.assertEqual(list(owners), spec["expected_declarations"])
        self.assertEqual(modules, spec["import_modules"])
        probe = ROOT / spec["probe"]
        contents = probe.read_text(encoding="utf-8")
        self.assertEqual(sha256(probe.read_bytes()), spec["probe_sha256"])
        require_no_proof_placeholders_or_axiom_commands(contents)
        self.assertEqual(re.findall(r"^import\s+(\S+)", contents, re.M), modules)
        self.assertEqual(re.findall(r"^#check\s+(\S+)", contents, re.M), list(owners))
        self.assertEqual(re.findall(r"^#print axioms\s+(\S+)", contents, re.M), list(owners))

    def test_all56_selected_source_signatures_and_named_transitive_axioms(self):
        self.test_frozen_56_rows_routes_pins_and_exact_declaration_ownership()
        spec = specification()
        self.assertIsNotNone(shutil.which("lake"), "Pinned Lean compiler is required")
        before = frozen_hashes(spec)
        self.assertEqual(before, spec["frozen_source_sha256"])
        probe = ROOT / spec["probe"]
        probe_hash = sha256(probe.read_bytes())
        self.assertEqual(probe_hash, spec["probe_sha256"])
        spec_hash = sha256(SPEC_PATH.read_bytes())
        driver_hash = sha256(Path(__file__).read_bytes())
        artifacts_before = provider_artifacts(spec)
        version = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                                 capture_output=True, text=True, timeout=60, check=True).stdout.strip()
        self.assertRegex(version, r"Lean \(version 4\.34\.0[,)]")
        head = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        git_status = subprocess.check_output(
            ["git", "status", "--porcelain", "--untracked-files=all"], cwd=ROOT, text=True).splitlines()
        command = ["lake", "env", "lean", str(probe)]
        started = time.monotonic()
        result = subprocess.run(command, cwd=ROOT, capture_output=True,
                                text=True, timeout=900, check=False)
        transcript = result.stdout + "\n" + result.stderr
        stage = {
            "source": spec["probe"], "source_sha256": probe_hash,
            "command": command, "exit_code": result.returncode,
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "stdout": result.stdout, "stderr": result.stderr,
            "compiler_output_sha256": sha256(transcript.encode()),
        }
        print("TRANCHE10_ALL56_COMPILER_STAGE " + json.dumps(stage, sort_keys=True), flush=True)
        self.assertEqual(result.returncode, 0, transcript[-16000:])
        self.assertNotIn("error:", transcript.lower(), transcript[-16000:])
        self.assertNotIn("sorryax", transcript.lower())
        axioms = parse_axiom_receipt(transcript, spec["expected_declarations"])
        self.assertEqual(frozen_hashes(spec), before)
        self.assertEqual(provider_artifacts(spec), artifacts_before)
        self.assertEqual(sha256(probe.read_bytes()), probe_hash)
        self.assertEqual(sha256(SPEC_PATH.read_bytes()), spec_hash)
        self.assertEqual(sha256(Path(__file__).read_bytes()), driver_hash)
        head_after = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip()
        self.assertEqual(head_after, head, "Git HEAD changed during source audit")
        git_status_after = subprocess.check_output(
            ["git", "status", "--porcelain", "--untracked-files=all"], cwd=ROOT, text=True).splitlines()
        evidence = {
            "format": "Permansson.CERT.Tranche10.All56NamedSourceReceipt.v1",
            "status": "PASS", "scope": spec["scope"], "acceptance_changes": 0,
            "case_count": 56, "case_owned_route_occurrences": 139,
            "distinct_named_declarations": len(axioms), "compiler": version,
            "checked_git_commit": head, "git_worktree_status": git_status,
            "git_worktree_status_after": git_status_after,
            "specification_sha256": spec_hash, "driver_sha256": driver_hash,
            "probe_sha256": probe_hash, "frozen_matrix_sha256": FROZEN_MATRIX_SHA256,
            "frozen_counts": FROZEN_COUNTS, "frozen_source_sha256": before,
            "provider_artifact_sha256": artifacts_before,
            "inputs_unchanged_across_compile": True,
            "positive_stage": stage, "axioms": axioms,
            "declaration_ownership": spec["declaration_ownership"],
            "case_ownership": [{"key": c["key"], "frozen_status": c["frozen_status"],
                                "expected_declarations": c["expected_declarations"],
                                "independent_acceptance_changed": False}
                               for c in spec["cases"]],
            "semantic_controls_executed_here": 0,
            "github_environment": {key: os.environ.get(key) for key in
                                   ("GITHUB_ACTIONS", "GITHUB_WORKFLOW", "GITHUB_RUN_ID",
                                    "GITHUB_RUN_ATTEMPT", "GITHUB_JOB", "GITHUB_SHA",
                                    "GITHUB_EVENT_NAME", "GITHUB_REF")},
            "limitations": spec["limitations"],
        }
        print("TRANCHE10_ALL56_CASE_RECEIPT " + json.dumps(evidence, sort_keys=True), flush=True)


if __name__ == "__main__":
    unittest.main()
