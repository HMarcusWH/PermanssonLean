"""C10 golden receipt deterministic emitter + tamper checks."""
import copy
from pathlib import Path
import tempfile
import json
import subprocess
import sys
import unittest
from c10_golden import six_input,create_golden
from c10_exact_execution import check_input,execute
from c10_verify_receipt import ReceiptError,verify_receipt

class C10GoldenTests(unittest.TestCase):
    def test_reproducible_identical_bytes(self):
        with tempfile.TemporaryDirectory() as a, tempfile.TemporaryDirectory() as b:
            create_golden(a);create_golden(b)
            for name in ('input.json','receipt.json'):
                self.assertEqual((Path(a)/name).read_bytes(),(Path(b)/name).read_bytes())
    def test_cli_emits_and_verifies_golden(self):
        with tempfile.TemporaryDirectory() as td:
            p=subprocess.run([sys.executable,str(Path(__file__).with_name('c10_golden.py')),td],capture_output=True,text=True)
            self.assertEqual(p.returncode,0,p.stderr)
            self.assertTrue(verify_receipt(json.loads((Path(td)/'receipt.json').read_text())))
    def test_all_six_expected_exact_fractions(self):
        with tempfile.TemporaryDirectory() as td:
            r=create_golden(td)
            self.assertEqual([m['margin'] for m in r['members']],['1','1/2','1/1000','0','0','0'])
            self.assertEqual((r['optimum'],r['selected'],r['ties']),('1','full',['full']))
    def test_second_run_exact_canonical_output(self):
        a=execute(check_input(six_input()))
        b=execute(check_input(six_input()))
        self.assertEqual(a,b)
    def test_rejected_tampered_golden(self):
        with tempfile.TemporaryDirectory() as td:
            r=create_golden(td)
            r['members'][1]['margin']='2/3'
            with self.assertRaises(ReceiptError):verify_receipt(r)
    def test_rejected_changed_original_comparison(self):
        with tempfile.TemporaryDirectory() as td:
            r=create_golden(td)
            r['normalized_input']['comparison']=[1]
            with self.assertRaises(ReceiptError):verify_receipt(r)
if __name__=='__main__': unittest.main()