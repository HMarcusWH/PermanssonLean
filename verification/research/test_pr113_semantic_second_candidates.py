"""PR113 original-case mathematical negative candidates (unreviewed).

Each test targets an original model/theorem and compiles its unchanged Lean
source as the positive control. The appended mathematically false assertion
must be rejected by the intended diagnostic, not by imports, tactics, timeouts,
or an unavailable compiler. No CI or scholarly approval is inferred here.
"""
from fractions import Fraction
from pathlib import Path
import shutil
import tempfile
import unittest

import final_closure_original_semantic_batch as batch
import final_closure_mutation_evidence as evidence

ROOT = Path(__file__).resolve().parents[2]
CASES = ("S-01", "M-01", "A-02", "D-01", "C11-01", "C11-02", "XPLUS-01")


class SecondOriginalNegativeCandidates(unittest.TestCase):
    def verify(self, case_id):
        self.assertIn(case_id, CASES)
        self.assertIsNotNone(shutil.which("lake"),
                             "pinned Lean required for semantic evidence")
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
                                         prefix="pr113-negative-") as folder:
            file = Path(folder) / "FalseOriginalCase.lean"
            file.write_bytes(mutant)
            negative = evidence.lean_result(file)
        self.assertTrue(evidence.verify_negative(
            positive, negative, original, mutant))

    def test_S_01_no_terminal_correction_is_false(self):
        # At horizon zero the omitted terminal term equals the initial V.
        self.assertEqual(Fraction(9, 10) ** 0 * Fraction(1, 2),
                         Fraction(1, 2))
        self.verify("S-01")

    def test_M_01_null_key_is_not_free_initial_support(self):
        # The source's different point-start treated path laws are NOT
        # contradicted by its almost-everywhere baseline agreement.
        self.verify("M-01")

    def test_A_02_identity_kernel_is_not_strictly_contractive(self):
        # Two distinct Dirac initial laws are both invariant under identity.
        ident = {0: {0: Fraction(1)}, 1: {1: Fraction(1)}}
        for state in (0, 1):
            self.assertEqual(ident[state], {state: Fraction(1)})
        self.verify("A-02")

    def test_D_01_hitting_is_not_residence(self):
        word = (False, True, False)
        self.assertTrue(any(word))
        self.assertFalse(any(all(word[i:i + 2])
                             for i in range(len(word) - 1)))
        self.verify("D-01")

    def test_C11_01_zero_dimensional_family_is_rejected(self):
        self.verify("C11-01")

    def test_C11_02_corrupted_stationary_report_is_rejected(self):
        self.verify("C11-02")

    def test_XPLUS_01_constructed_original_margin_is_not_zero(self):
        self.assertEqual(Fraction(1) - Fraction(0), Fraction(1))
        self.verify("XPLUS-01")


if __name__ == "__main__":
    unittest.main()
