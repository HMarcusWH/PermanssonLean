"""Three finite original-theory boundary negatives; candidate evidence only.

S-02 checks the original ActionTrace.Row information order rather than
granting foresight to a behavioral policy. Q-01 refutes uniform deterministic
lumpability without claiming every projected single-start process non-Markov.
A-01 distinguishes bounded 1-Lipschitz tests from a spurious global
unit-supnorm restriction. Lean compilation/independent review remain required.
"""
from pathlib import Path
from fractions import Fraction
import shutil
import tempfile
import unittest

import final_closure_original_semantic_batch as batch
import final_closure_mutation_evidence as evidence

ROOT = Path(__file__).resolve().parents[2]
CASES = ("S-02", "Q-01", "A-01")


class StructuralOriginalNegativeCandidates(unittest.TestCase):
    def verify(self, case_id):
        self.assertIn(case_id, CASES)
        self.assertIsNotNone(shutil.which("lake"),
                             "Lean/Lake required; mathematical evidence cannot be mocked")
        entry, mutant = batch.frozen_spec(case_id)
        original = (ROOT / entry["source"]).read_bytes()
        self.assertTrue(mutant.startswith(original))
        self.assertNotEqual(mutant, original)
        self.assertEqual(
            [line for line in mutant.splitlines() if line.startswith(b"import ")],
            [line for line in original.splitlines() if line.startswith(b"import ")]
        )
        positive = evidence.lean_result(ROOT / entry["source"])
        with tempfile.TemporaryDirectory(dir=ROOT / ".lake",
                                         prefix="pr113-structural-") as tmp:
            false_path = Path(tmp) / "FalseOriginalCase.lean"
            false_path.write_bytes(mutant)
            negative = evidence.lean_result(false_path)
        self.assertTrue(evidence.verify_negative(
            positive, negative, original, mutant))

    def test_S_02_clairvoyant_action_is_not_admissible_history_row(self):
        # Any pre-draw action mixture matches an independent fair coin at 1/2;
        # copying the yet-unobserved coin would instead match with certainty.
        for prob in (Fraction(0), Fraction(1, 4), Fraction(1)):
            self.assertEqual(prob / 2 + (1-prob) / 2, Fraction(1, 2))
        self.verify("S-02")

    def test_Q_01_fine_projection_does_not_always_lump(self):
        q = lambda x: x == 1
        step = lambda x: 1 if x == 0 else 0
        self.assertEqual(q(0), q(2))
        self.assertNotEqual(q(step(0)), q(step(2)))
        self.verify("Q-01")

    def test_A_01_unit_supnorm_is_not_correct_KR_test_class(self):
        # Four-unit ground distance; a <=1 absolute-value restriction
        # caps the two-point difference at 2.
        self.assertEqual(abs(Fraction(4)-Fraction(0)), 4)
        self.assertLess(2, 4)
        self.verify("A-01")


if __name__ == "__main__":
    unittest.main()
