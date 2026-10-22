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
