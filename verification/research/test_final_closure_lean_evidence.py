"""Source/axiom evidence exporter mocks are logic tests, not Lean certificates."""
from pathlib import Path
import json
import tempfile
import types
import unittest
from unittest import mock

import final_closure_lean_evidence as e


class LeanEvidenceTests(unittest.TestCase):
    def test_axiom_parser_is_literal_and_fail_closed(self):
        valid = "Demo.foo : True\nDemo.foo depends on axioms: [propext, Quot.sound]\n"
        self.assertEqual(e.parse_axioms(valid, "Demo.foo"),
                         ["propext", "Quot.sound"])
        for output in (
            valid.replace("Quot.sound", "sorryAx"),
            valid.replace("propext", "Foo.unsafeAxiom"),
            "Demo.foo : True\nerror: unknown identifier\n",
            "Demo.foo : True\nerror: maximum number of heartbeats\n",
            "Other.foo depends on axioms: []\n",
            "Demo.foo : True\n",
        ):
            with self.subTest(output=output[:50]):
                with self.assertRaises(e.CompilerEvidenceError):
                    e.parse_axioms(output, "Demo.foo")

    def test_missing_or_wrong_head_never_emits_certificate(self):
        with tempfile.TemporaryDirectory() as root:
            with mock.patch.object(e, "ROOT", Path(root)), \
                 mock.patch.object(e, "git_head", return_value="a"*40):
                with self.assertRaises(e.CompilerEvidenceError):
                    e.candidate_records("b"*40, Path(root)/"outside")
                with self.assertRaises(e.CompilerEvidenceError):
                    e.candidate_records("a"*40, Path(root)/"within")

    def test_positive_compiler_result_is_explicitly_not_acceptance(self):
        with tempfile.TemporaryDirectory() as root:
            base = Path(root)
            (base / ".lake").mkdir()
            (base / "PermanssonResearch").mkdir()
            (base / "PermanssonResearch" / "Simple.lean").write_text(
                "namespace Demo\n"
                "theorem foo : True := by trivial\n"
                "end Demo\n")
            claim_file = base / "claim_map.json"
            claim_file.write_text(json.dumps({
                "count": 11,
                "claims": [
                    {"claim_id": "Q1", "original_case_links": ["X-01"],
                     "declarations": [{"path": "PermanssonResearch/Simple.lean",
                                       "declaration": "Demo.foo"}]}
                ]}))
            external = base.parent / (base.name + "-outside")
            external.mkdir()
            self.addCleanup(lambda: __import__("shutil").rmtree(external, ignore_errors=True))
            output = ("Demo.foo : True\n"
                      "Demo.foo depends on axioms: []\n")
            process = types.SimpleNamespace(returncode=0, stdout=output, stderr="")
            with mock.patch.object(e, "ROOT", base), \
                 mock.patch.object(e, "MAP", claim_file), \
                 mock.patch.object(e, "git_head", return_value="a"*40), \
                 mock.patch.object(e, "run_probe", return_value=process):
                record = e.candidate_records("a"*40, external)
            self.assertEqual(record["status"], "COMPILER_ONLY_UNREVIEWED")
            self.assertEqual(record["proof_count"], 1)
            self.assertIsNone(record["compiler_axiom_receipts"][0]["check_run_id"])
            self.assertEqual(record["reviews"], [])


if __name__ == "__main__":
    unittest.main()
