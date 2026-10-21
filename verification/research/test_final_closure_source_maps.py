"""Candidate maps must exactly replay immutable original statements and sources."""
import json
from pathlib import Path
import unittest

import final_closure_case_map as cases
import final_closure_claim_map as claims
import final_closure_obligations_report as report
from final_closure_case_receipts import EvidenceError, statement_header


class OriginalSourceMapTests(unittest.TestCase):
    def test_original_45_map_has_literal_regenerability(self):
        expected = cases.OUTPUT.read_text(encoding="utf-8")
        self.assertEqual(expected, cases.render())
        data = cases.generate()
        self.assertEqual(data["original_cases"], 45)
        self.assertEqual(len(data["cases"]), 45)
        self.assertEqual(len({c["case_id"] for c in data["cases"]}), 45)
        self.assertTrue(all(c["effective_accepted"] is False
                            for c in data["cases"]))
        historical = json.loads((cases.SNAP/"acceptance_decisions.json").read_text())
        for old, new in zip(historical["cases"], data["cases"]):
            self.assertEqual(old["proof_declarations"],
                             new["historical_proof_declarations"])
            self.assertEqual(old["required_expected_result"],
                             new["required_expected_result"])
            self.assertEqual(old["historical_contract_ids"],
                             new["historical_contract_ids"])

    def test_eleven_claims_have_real_full_names_and_supports(self):
        self.assertEqual(claims.OUTPUT.read_text(encoding="utf-8"),
                         claims.render())
        data = claims.generate()
        self.assertEqual(data["count"], 11)
        self.assertEqual(len(data["claims"]), 11)
        self.assertFalse(any(c["accepted"] for c in data["claims"]))
        for c in data["claims"]:
            self.assertTrue(c["declarations"])
            for source in c["declarations"]:
                p = claims.ROOT / source["path"]
                self.assertTrue(p.is_file())
                self.assertTrue(statement_header(
                    p.read_text(encoding="utf-8"),
                    source["declaration"]))
        byid = {c["claim_id"]: c for c in data["claims"]}
        self.assertTrue(any("NonlinearPhaseBlindClassGeometry.lean" in d["path"]
                            for d in byid["N2"]["declarations"]))
        self.assertTrue(any(".ConcreteRestrictedBoolean." in d["declaration"]
                            for d in byid["D8"]["declarations"]))
        self.assertTrue(any(".FinalMatchedAsymmetry." in d["declaration"]
                            for d in byid["M3"]["declarations"]))
        self.assertTrue(any(".SourceBoundExactWitness." in d["declaration"]
                            for d in byid["Q3"]["declarations"]))

    def test_acceptance_obligations_report_is_deterministic_and_not_approved(self):
        text = report.render()
        self.assertEqual(report.OUTPUT.read_text(encoding="utf-8"), text)
        self.assertIn("pending: 15; partial scope: 30", text)
        self.assertIn("NOT ACCEPTED", text)

    def test_declared_local_name_outside_namespace_is_not_enough(self):
        source = ("namespace A.B\n"
                  "theorem token : True := by trivial\n"
                  "end A.B\n")
        self.assertEqual(statement_header(source, "A.B.token"),
                         "theorem token : True")
        for incorrect in ("Other.B.token", "A.B.unknown", "token"):
            with self.subTest(incorrect=incorrect):
                with self.assertRaises(EvidenceError):
                    statement_header(source, incorrect)


if __name__ == "__main__":
    unittest.main()
