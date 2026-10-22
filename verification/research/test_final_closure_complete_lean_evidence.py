"""All-case Lean theorem plan tests; no mock is a genuine compiler record."""
import copy
from pathlib import Path
import tempfile
import unittest

import final_closure_complete_lean_evidence as combined

CLAIMS = ("Q1", "Q2", "Q3", "M1", "M2", "M3", "N1", "N2",
          "N3", "D8", "D9")
P = "PermanssonResearch/Demo.lean"


def synthetic_source(root):
    repo = Path(root)
    (repo / "PermanssonResearch").mkdir()
    lines = ["namespace Demo"]
    lines += [f"theorem historical_{n} : True := by trivial" for n in range(45)]
    lines += [f"theorem claim_{k} : True := by trivial" for k in CLAIMS]
    lines += ["end Demo"]
    (repo / P).write_text("\n".join(lines), encoding="utf-8")
    cases = {"cases": [
        {"case_id": f"C-{i:02d}",
         "historical_proof_declarations": [
             {"path": P, "name": f"historical_{i-1}"}]}
        for i in range(1, 46)
    ]}
    claims = {"claims": [
        {"claim_id": cid, "declarations": [
            {"path": P, "declaration": f"Demo.claim_{cid}"}]}
        for cid in CLAIMS
    ]}
    return cases, claims


class AllCaseCompilerManifestTests(unittest.TestCase):
    def test_all_45_and_all_11_exact_qualified_names(self):
        with tempfile.TemporaryDirectory() as td:
            cases, claims = synthetic_source(td)
            got = combined.required_inventory(
                root=Path(td), case_map=cases, claim_map=claims)
            self.assertEqual(len(got), 56)
            self.assertEqual(len({c for row in got for c in row["case_ids"]}), 45)
            self.assertEqual({c for row in got for c in row["claim_ids"]},
                             set(CLAIMS))
            self.assertIn(("Demo.historical_0", "C-01"),
                          {(r["declaration"], c)
                           for r in got for c in r["case_ids"]})
            self.assertTrue(all(r["path"] == P and
                                r["declaration"].startswith("Demo.")
                                for r in got))

    def test_renamed_or_missing_historical_theorem_blocks_manifest(self):
        with tempfile.TemporaryDirectory() as td:
            cases, claims = synthetic_source(td)
            cases["cases"][8]["historical_proof_declarations"][0]["name"] = "invented"
            with self.assertRaises(combined.CompleteCompilerError):
                combined.required_inventory(
                    root=Path(td), case_map=cases, claim_map=claims)

    def test_duplicated_historical_ownership_case_is_blocked(self):
        with tempfile.TemporaryDirectory() as td:
            cases, claims = synthetic_source(td)
            cases["cases"][1]["case_id"] = "C-01"
            with self.assertRaises(combined.CompleteCompilerError):
                combined.required_inventory(
                    root=Path(td), case_map=cases, claim_map=claims)

    def test_claim_missing_one_of_exact_eleven_is_blocked(self):
        with tempfile.TemporaryDirectory() as td:
            cases, claims = synthetic_source(td)
            claims["claims"].pop()
            with self.assertRaises(combined.CompleteCompilerError):
                combined.required_inventory(
                    root=Path(td), case_map=cases, claim_map=claims)

    def test_deduplication_retains_all_case_and_claim_owners(self):
        with tempfile.TemporaryDirectory() as td:
            cases, claims = synthetic_source(td)
            cases["cases"][1]["historical_proof_declarations"][0]["name"] = "historical_0"
            claims["claims"][0]["declarations"][0]["declaration"] = "Demo.historical_0"
            got = combined.required_inventory(
                root=Path(td), case_map=cases, claim_map=claims)
            own = next(x for x in got if x["declaration"] == "Demo.historical_0")
            self.assertEqual(own["case_ids"], ["C-01", "C-02"])
            self.assertEqual(own["claim_ids"], ["Q1"])
            self.assertEqual(len(got), 54)

    def test_unrelated_private_lemmas_and_anonymous_instances_are_ignored(self):
        with tempfile.TemporaryDirectory() as td:
            cases, claims = synthetic_source(td)
            original = (Path(td)/P).read_text(encoding="utf-8")
            (Path(td)/P).write_text(
                "namespace NonPublic\n"
                "private theorem hidden : True := by trivial\n"
                "instance : Inhabited Unit := ⟨()⟩\n"
                "/- namespace Spoof\n"
                "theorem historical_0 : False := by contradiction\n"
                "-/\n"
                "-- theorem historical_0 : False := by contradiction\n"
                "end NonPublic\n" + original)
            result = combined.required_inventory(
                root=Path(td), case_map=cases, claim_map=claims)
            self.assertEqual(len(result), 56)
            self.assertEqual({r["declaration"] for r in result
                              if "C-01" in r["case_ids"]},
                             {"Demo.historical_0"})

    def test_targeting_private_lemma_cannot_resolve(self):
        with tempfile.TemporaryDirectory() as td:
            cases, claims = synthetic_source(td)
            source = Path(td)/P
            source.write_text(
                "namespace Demo\n"
                "private theorem secret : True := by trivial\n"
                "end Demo\n" + source.read_text(encoding="utf-8"))
            cases["cases"][0]["historical_proof_declarations"][0]["name"] = "secret"
            with self.assertRaisesRegex(combined.CompleteCompilerError,
                                        "unresolved"):
                combined.required_inventory(
                    root=Path(td), case_map=cases, claim_map=claims)

    def test_nested_comments_cannot_supply_fake_declaration(self):
        masked = (
            "namespace Outer\n"
            "/- test\n"
            "/- namespace Fake\n"
            "theorem fabricated : True := by trivial -/\n"
            "still hidden -/\n"
            "theorem real : True := by trivial\n"
            "end Outer\n"
        )
        self.assertEqual(combined.addressable_declarations(masked), ["Outer.real"])
        with self.assertRaisesRegex(combined.CompleteCompilerError, "unterminated"):
            combined.addressable_declarations("namespace Foo\n/- never ends")

    def test_namespace_ambiguity_never_assumes_theorem(self):
        with tempfile.TemporaryDirectory() as td:
            cases, claims = synthetic_source(td)
            with (Path(td)/P).open("a") as f:
                f.write("\nnamespace Other\n"
                        "theorem historical_0 : True := by trivial\n"
                        "end Other\n")
            with self.assertRaises(combined.CompleteCompilerError):
                combined.required_inventory(
                    root=Path(td), case_map=cases, claim_map=claims)

    def test_path_traversal_never_reads_untracked_external_source(self):
        with tempfile.TemporaryDirectory() as td:
            cases, claims = synthetic_source(td)
            cases["cases"][0]["historical_proof_declarations"][0]["path"] = "../Fake.lean"
            with self.assertRaises(combined.CompleteCompilerError):
                combined.required_inventory(
                    root=Path(td), case_map=cases, claim_map=claims)


if __name__ == "__main__":
    unittest.main()
