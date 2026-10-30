"""Source-bound private-stage Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_private_stage_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.private_stage import propose_private_stage
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.private_stage_emit import FORMAT,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/private_stage.v1.json'


def fixture():
    raw=json.loads(EXAMPLE.read_text())
    return raw,propose_private_stage(raw)


class PrivateStageEmitTests(unittest.TestCase):
    def test_example_emits_bound_instance(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['theorem_names'],['receipt_checked','hs','hp','value_greatest','private_saddle',
                                                'solver_value','pure_controls','revealed_control'])
        self.assertIn('def v : ℚ := (1 : ℚ)',source)
        self.assertIn('def r : ℚ := ((1 : ℚ) / (2 : ℚ))',source)
        self.assertIn("def q : Fin 2 → ℚ := fun t => (if t = (0 : Fin 2) then ((3 : ℚ) / (5 : ℚ))",source)
        self.assertIn('theorem solver_value : (solvePrivateStage Q).map (fun x => x none) = some v :=',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_singleton_dimensions_use_unreferenced_binders(self):
        raw={'format':'Permansson.App.PrivateStageRequest.v1','labels':{'controls':['a'],'nature':['x']},
             'payoff':[['-5/3']]}
        source,_=emit_source(raw,propose_private_stage(raw))
        self.assertIn('def Q : Fin 1 → Fin 1 → ℚ := fun _t _c => ((-5 : ℚ) / (3 : ℚ))',source)
        self.assertIn('def p : Fin 1 → ℚ := fun _c => (1 : ℚ)',source)

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        for key,value in (('value','11/10'),('nature_mixture',['1/2','1/2']),('lean_status','PASS'),
                          ('pure_control_value','1')):
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
            result=check_family('private-stage',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.PrivateStageSourceRecheck.v1')
            lean=base/'out/ReifiedPrivateStage.lean'
            text=lean.read_text()
            changed=text.replace('def v : ℚ := (1 : ℚ)','def v : ℚ := (2 : ℚ)',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('private-stage',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'PRIVATE_STAGE_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
