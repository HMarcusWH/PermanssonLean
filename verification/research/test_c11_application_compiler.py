"""Mandatory genuine Lean replay for periodic and multichain C11 application."""
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'apps/permansson/closure-successor-c11/cli.py'
EX=APP.parent/'examples'
spec=importlib.util.spec_from_file_location('c11_application_proof_replay',APP)
cli=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=cli
spec.loader.exec_module(cli)


class C11GenuineLeanReplay(unittest.TestCase):
    def test_periodic_and_multichain_sources_kernel_check(self):
        for filename,count in [('periodic_two_state.json',1),
                               ('multiclass_three_state.json',2)]:
            with self.subTest(input=filename),tempfile.TemporaryDirectory() as td:
                out=Path(td)/'new'
                rc=cli.run_cli([str(EX/filename),'--mode','replay','--output',str(out)])
                self.assertEqual(rc,0,'actual Lean or one source identity gate failed')
                result=json.loads((out/'result.json').read_text())
                self.assertEqual(result['lean_status'],
                                 'KERNEL_CHECKED_REIFIED_STATIONARY_FAMILY')
                self.assertEqual(result['bottom_classes'],count)
                self.assertEqual(len(result['axioms']),4*count+1)
                self.assertTrue((out/'C11ReifiedStationary.lean').exists())
                self.assertFalse(result['scientific_claims_verified'])
                self.assertEqual(result['empirical_identification'],'NOT_IDENTIFIED')
                self.assertEqual(result['compiler_exit'],0)


if __name__=='__main__':unittest.main()
