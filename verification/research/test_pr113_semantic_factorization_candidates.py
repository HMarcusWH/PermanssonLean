"""A04/A05 conditional boundary candidates, not source-review acceptance.

A04 is an explicit four-output input-necessity counterexample and must NOT
be misreported as a fully realized canonical four-path-law comparison.
A05 compares the SAME finite kernel's stationary mass with the literal
infinite physical survival event. It does NOT replace the original property
or construct a new empirical GR certificate.
"""
from fractions import Fraction as Q
from pathlib import Path
import shutil
import tempfile
import unittest

import final_closure_original_semantic_batch as batch
import final_closure_mutation_evidence as evidence

ROOT = Path(__file__).resolve().parents[2]


class FactorizationBoundaryCandidates(unittest.TestCase):
    def verify(self, case_id):
        self.assertIn(case_id, ("A-04", "A-05"))
        self.assertIsNotNone(shutil.which("lake"),
                             "pinned Lean must execute; no fake compiler receipt")
        entry, mutant = batch.frozen_spec(case_id)
        original = (ROOT / entry["source"]).read_bytes()
        self.assertTrue(mutant.startswith(original))
        self.assertEqual(
            [x for x in mutant.splitlines() if x.startswith(b"import ")],
            [x for x in original.splitlines() if x.startswith(b"import ")]
        )
        positive = evidence.lean_result(ROOT / entry["source"])
        with tempfile.TemporaryDirectory(dir=ROOT / ".lake",
                                         prefix="pr113-factor-") as tmp:
            path = Path(tmp) / "FalseAssertion.lean"
            path.write_bytes(mutant)
            negative = evidence.lean_result(path)
        self.assertTrue(evidence.verify_negative(
            positive, negative, original, mutant))

    def test_A_04_missing_fourth_output_changes_margin(self):
        gap = lambda a,b,c,d: abs(abs(c-d)-abs(a-b))
        self.assertEqual(gap(Q(0),Q(1),Q(0),Q(0)),Q(1))
        self.assertEqual(gap(Q(0),Q(1),Q(0),Q(1)),Q(0))
        self.verify("A-04")

    def test_A_05_stationary_mass_is_not_forever_survival(self):
        q = Q(99,100)
        pi = (q,1-q)
        P = ((q,1-q),(q,1-q))
        self.assertEqual(sum(pi),1)
        self.assertTrue(all(sum(pi[i]*P[i][j] for i in range(2))==pi[j]
                            for j in range(2)))
        self.assertEqual(q**1,q)
        self.assertLess(q**100,q)
        self.verify("A-05")


if __name__ == "__main__":
    unittest.main()
