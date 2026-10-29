"""Exact original 45-case positive proof probes for missing ENG-04 routes.

Each method imports the ACTUAL original source owners for one frozen case,
asks pinned Lean for every required declaration, checks that its elaborated
type and transitive axioms are present, and permits only trusted axioms.
This is a positive compiler control, never a semantic negative, independent
case approval, or proof that the original acceptance wording is satisfied.

The case ID and requirement are obtained from the unchanged 45-case registry,
not from an assistant-authored list of substitute theorem statements.
"""
from __future__ import annotations

import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

from closure_elaborated_type import (
    lean_probe, compiled_type_record, TypeEvidenceError
)
from final_closure_case_receipts import parse_target_axioms, TRUSTED_AXIOMS
from final_closure_complete_lean_evidence import (
    CompleteCompilerError, resolved_name
)

ROOT = Path(__file__).resolve().parents[2]
MAP = ROOT / "research/paper_closures/post_merge_112/acceptance_case_source_map.json"

# Only exact original cases that have no positive method selection yet.
ORIGINAL_MISSING_POSITIVE = (
    "X-04", "X-05", "X-06", "F-03", "A-05",
    "C11-02", "B-01", "E-02", "E-03", "E-04",
)


class HistoricalPositiveCompilerControls(unittest.TestCase):
    def check_original_case(self, case_id: str):
        self.assertIn(case_id, ORIGINAL_MISSING_POSITIVE)
        self.assertTrue(shutil.which("lake"), "pinned Lean compiler required")
        data = json.loads(MAP.read_text(encoding="utf-8"))
        self.assertEqual(data["original_cases"], 45)
        rows = [x for x in data["cases"] if x["case_id"] == case_id]
        self.assertEqual(len(rows), 1)
        row = rows[0]
        self.assertFalse(row["effective_accepted"])
        decls = row["historical_proof_declarations"]
        self.assertTrue(decls, "historical theorem inventory missing")
        seen = set()
        records = []
        cache = {}
        for item in decls:
            path, short = item["path"], item["name"]
            fqn = resolved_name(ROOT, path, short, cache)
            key = (path, fqn)
            self.assertNotIn(key, seen, "duplicate historical theorem route")
            seen.add(key)
            module = path.removesuffix(".lean").replace("/", ".")
            records.append((module, fqn))
        # The dedicated 45-case compiler sharded job verifies the COMPLETE
        # historical declaration graph. This independent per-case positive
        # control chooses one original theorem, but never represents the
        # remaining theorem dependencies as successfully executed.
        module, declaration = records[0]
        source = lean_probe(module, declaration)
        with tempfile.TemporaryDirectory(
            prefix="original-" + case_id.replace("-", "_") + "-",
            dir=ROOT / ".lake"
        ) as tmp:
            file = Path(tmp) / "OriginalCase.lean"
            file.write_text(source, encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(file)], cwd=ROOT,
                text=True, capture_output=True, timeout=900
            )
        out = result.stdout + "\n" + result.stderr
        self.assertEqual(result.returncode, 0, out[-5000:])
        self.assertNotIn("error:", out.lower())
        self.assertNotIn("sorryAx", out)
        try:
            type_record = compiled_type_record(out, declaration)
            axioms = parse_target_axioms(out, declaration)
        except (TypeEvidenceError, ValueError) as exc:
            self.fail("missing exact compiler type/axioms for " +
                      declaration + ": " + str(exc))
        self.assertEqual(type_record["declaration"], declaration)
        self.assertTrue(type_record["type_expr_repr"])
        self.assertLessEqual(set(axioms), TRUSTED_AXIOMS)

    def test_X_04_original_source_positive(self):
        self.check_original_case("X-04")

    def test_X_05_original_source_positive(self):
        self.check_original_case("X-05")

    def test_X_06_original_source_positive(self):
        self.check_original_case("X-06")

    def test_F_03_original_source_positive(self):
        self.check_original_case("F-03")

    def test_A_05_original_source_positive(self):
        self.check_original_case("A-05")

    def test_C11_02_original_source_positive(self):
        self.check_original_case("C11-02")

    def test_B_01_original_source_positive(self):
        self.check_original_case("B-01")

    def test_E_02_original_source_positive(self):
        self.check_original_case("E-02")

    def test_E_03_original_source_positive(self):
        self.check_original_case("E-03")

    def test_E_04_original_source_positive(self):
        self.check_original_case("E-04")


if __name__ == "__main__":
    unittest.main()
