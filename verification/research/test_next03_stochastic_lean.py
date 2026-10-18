"""A stochastic-but-wrong X1 literal must fail the ACTUAL kernel-backed equality.

This is separate from the old corrupt-row-sum mutant. Missing Lean is FAILURE,
not an expected negative mathematical result; live CI is required.
"""
from __future__ import annotations
from fractions import Fraction
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
SOURCE=ROOT/'PermanssonResearch/X1/ExactMatrixTables.lean'
LEDGER=ROOT/'research/paper_closures/spec/certificates/x1_exact_tables.json'
EXPECTED_OLD='![0, 0, 3/4, 1/4, 0, 0,'
EXPECTED_MUTANT='![0, 0, 2/4, 2/4, 0, 0,'
INVALID = re.compile(r'unknown (?:module|identifier|constant|tactic)|file not found|failed to import|\bsyntax error\b|unexpected token|failed to synthesize|heartbeat|out of memory|timed out|object file',re.I)
SEMANTIC = re.compile(r"tactic .?decide.? proved that the proposition|unsolved goals|Tactic .?decide.? failed|failed to prove",re.I)

class StochasticWrongX1Literal(unittest.TestCase):
    def test_actual_kernel_equality_rejects_normalized_wrong_row(self):
        self.assertTrue(SOURCE.exists(), 'real X1 matrix source missing')
        self.assertTrue(LEDGER.exists(), 'frozen exact X1 certificate missing')
        import generate_x1_matrix_tables as generator
        source=SOURCE.read_text(encoding='utf-8')
        self.assertEqual(source, generator.render(), 'source must be byte-identical to canonical certificate renderer')
        self.assertGreater(source.count(EXPECTED_OLD),0)
        mutant=source.replace(EXPECTED_OLD,EXPECTED_MUTANT,1)
        self.assertNotEqual(mutant,source)
        self.assertEqual(mutant.count('import '),source.count('import '))
        self.assertEqual(mutant.count('theorem matrix_eq_entry'),1)
        # First changed E-baseline row is 0+0+1/2+1/2=1, nonnegative.
        row=[Fraction('0'),Fraction('0'),Fraction('2/4'),Fraction('2/4')]+[Fraction('0')]*14
        self.assertEqual(sum(row),Fraction(1))
        self.assertTrue(all(0<=x<=1 for x in row))
        import shutil
        self.assertIsNotNone(shutil.which('lake'), 'compiler unavailable: cannot certify semantic rejection')
        with tempfile.TemporaryDirectory(prefix='next03_x1_',dir=ROOT/'.lake') as tmp:
            file=Path(tmp)/'WrongButStochastic.lean'
            file.write_text(mutant,encoding='utf-8',newline='\n')
            # Compile positive exact source FIRST. No false-positive failure from a
            # broken environment can count as rejecting the mutation.
            positive=subprocess.run(['lake','env','lean',str(SOURCE)],cwd=ROOT,capture_output=True,text=True,
                                    encoding='utf-8',timeout=600)
            self.assertEqual(positive.returncode,0,(positive.stdout+positive.stderr)[-4000:])
            negative=subprocess.run(['lake','env','lean',str(file)],cwd=ROOT,capture_output=True,text=True,
                                    encoding='utf-8',timeout=600)
            output=negative.stdout+'\n'+negative.stderr
            self.assertNotEqual(negative.returncode,0,'stochasticly wrong X1 matrix compiled as theorem')
            self.assertIsNone(INVALID.search(output),'invalid syntax/import/resource rejection is not semantic evidence')
            self.assertIsNotNone(SEMANTIC.search(output),'not the intended kernel-equality proof rejection')
            # The unchanged baseline-corner theorem is true; matrix_eq_entry
            # must do the work, not a malformed literal or row-sum guard.
            self.assertIn('matrix_eq_entry',source)
            self.assertIn('matrix_eq_entry',mutant)

if __name__=='__main__':unittest.main()
