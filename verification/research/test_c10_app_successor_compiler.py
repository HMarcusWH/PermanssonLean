"""NEXT-07: source-bound real Lean replay of one supported C10 input.

Mandatory in Research CI. Never skip or replace with mocked subprocess,
status JSON, previous archived output, or Python-only evaluation.
"""
from __future__ import annotations
from pathlib import Path
import json
import os
import subprocess
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
CLI=ROOT/'apps/permansson/closure-successor/cli.py'
INPUT=ROOT/'apps/permansson/closure-successor/examples/frozen_six_state.json'

class ActualLeanProofReplay(unittest.TestCase):
    def test_supported_input_replays_genuine_proof_kernel(self):
        with tempfile.TemporaryDirectory(prefix='permannson-c10-replay-') as d:
            out=Path(d)/'replay'
            command=[sys.executable,str(CLI),str(INPUT),'--mode','replay','--output',str(out)]
            proc=subprocess.run(command,cwd=ROOT,capture_output=True,text=True,encoding='utf-8',timeout=720,check=False)
            self.assertEqual(proc.returncode,0,proc.stdout+'\n'+proc.stderr[-4000:])
            status=json.loads(proc.stdout.strip())
            self.assertTrue(status['ok'])
            self.assertEqual(status['lean_status'],'KERNEL_CHECKED')
            result=json.loads((out/'result.json').read_text())
            self.assertEqual(result['source']['git_head'],subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip())
            self.assertEqual(result['lean_status'],'KERNEL_CHECKED')
            self.assertFalse(result['scientific_claims_verified'])
            self.assertEqual(result['empirical_identification'],'NOT_IDENTIFIED')
            self.assertEqual(result['numeric_optimum'],'1')
            self.assertEqual(result['numeric_selected'],'full')
            self.assertIn('reifiedGolden_original_margins',result['axioms'])
            self.assertTrue((out/'lean.stdout.txt').is_file())
            self.assertTrue((out/'C10ReifiedGolden.lean').is_file())

if __name__=='__main__': unittest.main()
