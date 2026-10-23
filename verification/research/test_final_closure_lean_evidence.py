"""Source/axiom evidence exporter mocks are logic tests, not Lean certificates."""
from pathlib import Path
import json
import re
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

    def test_unrelated_last_axiom_record_never_replaces_target(self):
        for output in (
            "Demo.foo : True\nOther.foo depends on axioms: []\n",
            "Demo.foo depends on axioms: []\nOther.foo depends on axioms: []\n",
            "Demo.foo depends on axioms: []\nDemo.foo does not depend on any axioms\n",
        ):
            with self.subTest(output=output), self.assertRaises(e.CompilerEvidenceError):
                e.parse_axioms(output, "Demo.foo")
        self.assertEqual(e.parse_axioms(
            "Demo.foo : True\nDemo.foo does not depend on any axioms\n",
            "Demo.foo"), [])

    def test_quoted_single_target_keeps_real_lean_multiline_output(self):
        log = ("PERMANSSON_ELABORATED_TYPE_V1_BEGIN\n"
               "NAME=Demo.foo\nKIND=theorem\nUNIVERSES=[]\n"
               "TYPE=Expr.const `True []\n"
               "PERMANSSON_ELABORATED_TYPE_V1_END\n"
               "info: Demo.lean:3:0: 'Demo.foo' depends on axioms: "
               "[propext,\n Classical.choice.{u},\n Quot.sound]\n")
        self.assertEqual(set(e.parse_axioms(log, "Demo.foo")),
                         {"propext", "Classical.choice", "Quot.sound"})
        with self.assertRaises(e.CompilerEvidenceError):
            e.parse_axioms(log + "'Other.foo' depends on axioms: []\n",
                           "Demo.foo")

    def test_missing_or_wrong_head_never_emits_certificate(self):
        with tempfile.TemporaryDirectory() as root:
            with mock.patch.object(e, "ROOT", Path(root)), \
                 mock.patch.object(e, "git_head", return_value="a"*40):
                with self.assertRaises(e.CompilerEvidenceError):
                    e.candidate_records("b"*40, Path(root)/"outside")
                with self.assertRaises(e.CompilerEvidenceError):
                    e.candidate_records("a"*40, Path(root)/"within")

    def test_forged_count_with_one_claim_is_rejected(self):
        with tempfile.TemporaryDirectory() as root:
            base = Path(root)
            fake = base / "map.json"
            fake.write_text(json.dumps({
                "count": 11, "claims": [{
                    "claim_id": "Q1", "original_case_links": ["X-01"],
                    "declarations": [{"path": "Simple.lean",
                                      "declaration": "Demo.foo"}],
                    "test_source_candidates": ["verification/research/test_fake.py"],
                }]
            }))
            outside = base.parent / (base.name + "-evidence")
            with mock.patch.object(e, "ROOT", base), \
                 mock.patch.object(e, "MAP", fake), \
                 mock.patch.object(e, "git_head", return_value="a"*40):
                with self.assertRaises(e.CompilerEvidenceError):
                    e.candidate_records("a"*40, outside)

    def test_complete_mocked_claim_map_only_emits_unreviewed_candidates(self):
        with tempfile.TemporaryDirectory() as root:
            base = Path(root)
            (base / ".lake").mkdir()
            (base / "PermanssonResearch").mkdir()
            (base / "verification/research").mkdir(parents=True)
            (base / "verification/research/test_fake.py").write_text(
                "def test_fake(): pass\n")
            declarations = [f"Demo.foo_{i}" for i in range(11)]
            (base / "PermanssonResearch/Simple.lean").write_text(
                "namespace Demo\n" +
                "".join(f"theorem foo_{i} : True := by trivial\n"
                        for i in range(11)) + "end Demo\n")
            ids = e.CLAIM_IDS
            claim_file = base / "claim_map.json"
            claim_file.write_text(json.dumps({
                "count": 11,
                "claims": [{
                    "claim_id": cid, "original_case_links": ["X-01"],
                    "declarations": [{"path": "PermanssonResearch/Simple.lean",
                                      "declaration": decl}],
                    "test_source_candidates": ["verification/research/test_fake.py"],
                } for cid, decl in zip(ids, declarations)]
            }))
            external = base.parent / (base.name + "-outside")
            external.mkdir()
            self.addCleanup(lambda: __import__("shutil").rmtree(
                external, ignore_errors=True))
            def fake_compiler(probe):
                decl = re.search(r"let nm : Name := `([^\n]+)", probe.read_text()).group(1)
                output = (
                    "PERMANSSON_ELABORATED_TYPE_V1_BEGIN\n"
                    f"NAME={decl}\nKIND=theorem\nUNIVERSES=[]\n"
                    "TYPE=Expr.const `True []\n"
                    "PERMANSSON_ELABORATED_TYPE_V1_END\n"
                    f"{decl} depends on axioms: []\n"
                )
                return types.SimpleNamespace(
                    returncode=0, stdout=output, stderr="")
            with mock.patch.object(e, "ROOT", base), \
                 mock.patch.object(e, "MAP", claim_file), \
                 mock.patch.object(e, "git_head", return_value="a"*40), \
                 mock.patch.object(e, "run_probe", side_effect=fake_compiler):
                record = e.candidate_records("a"*40, external)
            self.assertEqual(record["status"], "COMPILER_ONLY_UNREVIEWED")
            self.assertEqual(record["proof_count"], 11)
            self.assertTrue(all(row["check_run_id"] is None
                                for row in record["compiler_axiom_receipts"]))
            self.assertEqual(record["reviews"], [])


if __name__ == "__main__":
    unittest.main()
