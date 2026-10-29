"""The source inventory must include every added theorem and never accept it."""
from pathlib import Path
import json
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "verification/research"))
import final_closure_generate as generator

class ClosureGeneratorTests(unittest.TestCase):
    def test_all_eleven_closure_modules_present_and_directly_imported(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory)/"current_source.json"
            report = generator.generate(path)
            self.assertEqual(report["original_case_count"],45)
            self.assertEqual(len(report["source_rows"]),11)
            self.assertTrue(all(r["source_sha256"] for r in report["source_rows"]))
            self.assertTrue(all(r["imported_by_research_root"] for r in report["source_rows"]))
            self.assertGreater(sum(len(r["declarations"]) for r in report["source_rows"]),11)
            self.assertEqual(report["status"],"CANDIDATE_UNREVIEWED")
            self.assertEqual(report["source_bound_ci"],[])
            self.assertEqual(report["independent_reviews"],[])
            self.assertTrue(all(r["compiled_head_sha"] is None for r in report["source_rows"]))
            self.assertEqual(json.loads(path.read_text())["format"],
                             "Permansson.FinalClosureCandidateObservation.v2")

    def test_statement_hashes_have_strict_byte_identity(self):
        source = ROOT/"PermanssonResearch/MultiAgent/MeasurableProductTwoMatchedProtocols.lean"
        entries = generator.exact_statements(source)
        self.assertIn("matched_closed_kernel_two",{e["declaration"] for e in entries})
        self.assertTrue(all(len(e["statement_sha256"])==64 for e in entries))
        self.assertTrue(all(e["compiler_result"]=="NOT_VERIFIED" for e in entries))

if __name__ == "__main__":
    unittest.main()
