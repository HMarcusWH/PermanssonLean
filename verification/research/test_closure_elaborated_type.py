"""Test exact elaborated-type export; mock probes are never proof receipts."""
import shutil
import subprocess
from pathlib import Path
import tempfile
import unittest

import closure_elaborated_type as et

ROOT = Path(__file__).resolve().parents[2]


class ElaboratedCompilerTypeTests(unittest.TestCase):
    def test_type_parser_preserves_target_and_entire_ast(self):
        log = (et.BEGIN + "\n"
               "NAME=Demo.foo\nKIND=theorem\nUNIVERSES=[u]\n"
               "TYPE=Expr.forallE (x : Type u) (more := x)\n" +
               et.END + "\n")
        record = et.compiled_type_record(log, "Demo.foo")
        self.assertIn("more := x", record["type_expr_repr"])
        first_hash = et.elaborated_type_sha256(record)
        later_hypothesis = et.compiled_type_record(
            log.replace("more := x", "more := (x, x)"), "Demo.foo")
        self.assertNotEqual(first_hash, et.elaborated_type_sha256(later_hypothesis))
        for invalid in (
            log + log,
            log.replace("Demo.foo", "Other.foo"),
            log.replace("KIND=theorem", "KIND=invented"),
            log.replace("TYPE=Expr.forallE (x : Type u) (more := x)", "TYPE= "),
        ):
            with self.subTest(invalid=invalid[-50:]), self.assertRaises(et.TypeEvidenceError):
                et.compiled_type_record(invalid, "Demo.foo")

    def test_full_compiler_probe_of_builtin_lean_theorem(self):
        # This is a real Lean invocation, not simulated stdout. It is required
        # by Research CI after installing the project's pinned toolchain.
        self.assertIsNotNone(shutil.which("lake"),
                             "pinned Lake is required for elaborated type evidence")
        root_lake = ROOT / ".lake"
        self.assertTrue(root_lake.is_dir(), "project Lean environment is missing")
        with tempfile.TemporaryDirectory(prefix="closure-type-", dir=root_lake) as tmp:
            source = Path(tmp) / "Audit.lean"
            source.write_text(et.lean_probe("Lean", "Nat.add_comm"), encoding="utf-8")
            result = subprocess.run(
                ["lake", "env", "lean", str(source)],
                cwd=ROOT, text=True, capture_output=True, timeout=120)
            self.assertEqual(
                result.returncode, 0,
                (result.stdout + result.stderr)[-4000:])
            record = et.compiled_type_record(
                result.stdout + "\n" + result.stderr, "Nat.add_comm")
            self.assertEqual(record["declaration_kind"], "theorem")
            self.assertIn("forallE", record["type_expr_repr"])
            self.assertEqual(len(et.elaborated_type_sha256(record)), 64)


if __name__ == "__main__":
    unittest.main()
