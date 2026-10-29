"""Unreviewed PR113 original-case semantic-negative candidate checks.

These checks retain the ORIGINAL Lean source and append a single false
mathematical claim drawn from its source-bound counterexample. They are not
independent case acceptance, a signed receipt, or evidence of an executed CI
job. A clean original compilation is required before negative rejection.
"""
from pathlib import Path
import shutil
import tempfile
import unittest

import final_closure_original_semantic_batch as batch
import final_closure_mutation_evidence as evidence

ROOT = Path(__file__).resolve().parents[2]
CASES = ("A-03", "C-01", "D-07", "E-01")


class OriginalBoundaryNegativeCandidates(unittest.TestCase):
    def verify(self, case_id):
        self.assertIn(case_id, CASES)
        if shutil.which("lake") is None:
            self.fail("pinned Lean/Lake compiler required; no mock certification")
        entry, mutated = batch.frozen_spec(case_id)
        source = ROOT / entry["source"]
        original = source.read_bytes()
        self.assertTrue(mutated.startswith(original))
        self.assertNotEqual(mutated, original)
        self.assertEqual(mutated.count(b"\nimport "), original.count(b"\nimport "))
        positive = evidence.lean_result(source)
        with tempfile.TemporaryDirectory(prefix="pr113-boundary-",
                                         dir=ROOT / ".lake") as temporary:
            mutant_path = Path(temporary) / "OriginalFalse.lean"
            mutant_path.write_bytes(mutated)
            negative = evidence.lean_result(mutant_path)
        self.assertTrue(evidence.verify_negative(
            positive, negative, original, mutated))

    def test_A_03_unbounded_TV_does_not_bound_W1(self):
        self.verify("A-03")

    def test_C_01_bounded_descriptor_occupation_nonconvergence(self):
        self.verify("C-01")

    def test_D_07_finite_survival_does_not_imply_infinite_safety(self):
        self.verify("D-07")

    def test_E_01_seam_invisibility_does_not_force_rank_one(self):
        # The original exact rational rank-two matrix refutes the false
        # rank-one universal conclusion independently of Lean diagnostics.
        matrix = ((0, 1), (1, 2))
        self.assertTrue(all(
            matrix[i][j] - matrix[i][0] - matrix[0][j] + matrix[0][0] == 0
            for i in range(2) for j in range(2)))
        self.assertEqual(matrix[0][0] * matrix[1][1] -
                         matrix[0][1] * matrix[1][0], -1)
        self.verify("E-01")


if __name__ == "__main__":
    unittest.main()
