"""Source-bound adaptive admitted-block Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_adaptive_live_lean.py; these tests need no Lean.
"""
from __future__ import annotations
from copy import deepcopy
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.engines.adaptive import propose_adaptive
from permansson_app.errors import AppError
from permansson_app.proof.adaptive_emit import FORMAT,emit_files,emit_source
from permansson_app.proof.control_source_check import check_family

EXAMPLE=APP/'src/permansson_app/data/examples/adaptive.v1.json'


def fixture():
    raw=json.loads(EXAMPLE.read_text())
    return raw,propose_adaptive(raw)


class AdaptiveEmitTests(unittest.TestCase):
    def test_example_emits_bound_instance(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['theorem_names'][-3:],['receipt_checked','adaptive_optimal_0','adaptive_optimal_2'])
        self.assertIn('block_2_alpha_rows',meta['theorem_names'])
        self.assertIn('def sys : FiniteControlSystem (Fin 3) (2 * 2) := blockSystem (inducedMatrix base) members',source)
        self.assertIn('def M : Monitor (Fin 3) (2 * 2) Bool := regionMonitor region true',source)
        self.assertIn('def region : Finset (Fin (2 * 2)) := ({0, 2} : Finset (Fin 4))',source)
        self.assertEqual(meta['scope']['policy_class'],'FULL_HISTORY_BEHAVIORAL_OVER_DECLARED_BLOCKS')
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_single_block_and_lean_horizon_scope(self):
        raw,_=fixture();raw['grammar']['admitted_blocks']=[[]]
        source,_=emit_source(raw,propose_adaptive(raw))
        self.assertIn('def members : Fin 1 → RationalMarkovMatrix (2 * 2) := fun _i => inducedMatrix block_0',source)
        raw,_=fixture();raw['grammar']['horizon']=7
        with self.assertRaises(AppError) as raised:emit_source(raw,propose_adaptive(raw))
        self.assertEqual(raised.exception.code,'ADAPTIVE_REIFY_SCOPE')

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        for key,value in (('adaptive_values',['3/8','3/8']),('adaptivity_gain',['0','0']),('lean_status','PASS')):
            bad=deepcopy(receipt);bad[key]=value
            with self.subTest(key=key),self.assertRaises(AppError):
                emit_source(raw,bad)

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('adaptive',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.AdaptiveSourceRecheck.v1')
            lean=base/'out/ReifiedAdaptive.lean'
            text=lean.read_text()
            changed=text.replace('regionMonitor region true','regionMonitor region false',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('adaptive',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'ADAPTIVE_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
