"""Source-bound rational algebra Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_algebra_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.algebra import propose_algebra
from permansson_app.errors import AppError
from permansson_app.proof.algebra_emit import FORMAT,emit_files,emit_source
from permansson_app.proof.control_source_check import check_family

EXAMPLE=APP/'src/permansson_app/data/examples/algebra.v1.json'
R='Permansson.App.RationalAlgebraRequest.v1'


class AlgebraEmitTests(unittest.TestCase):
    def test_profiles_emit_their_theorems(self):
        cases={'schur':(json.loads(EXAMPLE.read_text()),['schur_checked','shell_complement']),
               'seam':({'format':R,'profile':'seam','H':[['3','3'],['3','3']],'pivot':0},
                       ['seam_checked','seam_rank','diagonal_checked','common_mode']),
               'singular':({'format':R,'profile':'singular','H':[['1','1'],['1','1']],'b':['1','0'],'c':'3'},
                           ['incompatible_checked','no_preimage_negative_direction']),
               'gram':({'format':R,'profile':'gram','x':['1','0'],'y':['1','1'],'c':'2'},
                       ['gram_checked','gram_separation'])}
        for name,(raw,names) in cases.items():
            with self.subTest(name=name):
                source,meta=emit_source(raw,propose_algebra(raw))
                self.assertEqual(meta['format'],FORMAT)
                self.assertEqual(meta['theorem_names'],names)
                self.assertEqual(meta['scope']['feature_identification'],'NOT_ESTABLISHED_EXPLICIT_PREMISE')
                self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))
                for flag in ('compiler_evidence_authenticated','independent_math_certification',
                             'empirical_identification','application_release_authorized'):
                    self.assertIs(meta[flag],False)

    def test_failed_premises_are_not_bound(self):
        for raw in ({'format':R,'profile':'seam','H':[['1','2','0'],['2','0','0'],['0','0','5']],'pivot':1},
                    {'format':R,'profile':'gram','x':['1','0'],'y':['2','0'],'c':'1'}):
            with self.subTest(profile=raw['profile']),self.assertRaises(AppError) as raised:
                emit_source(raw,propose_algebra(raw))
            self.assertEqual(raised.exception.code,'ALGEBRA_REIFY_SCOPE')

    def test_tampered_receipts_never_emit(self):
        raw=json.loads(EXAMPLE.read_text());receipt=propose_algebra(raw)
        for key,value in (('shell_complement',[['3/2']]),('lean_status','PASS')):
            bad=deepcopy(receipt);bad[key]=value
            with self.subTest(key=key),self.assertRaises(AppError):
                emit_source(raw,bad)

    def test_source_recheck_binds_original_bytes(self):
        raw=json.loads(EXAMPLE.read_text());receipt=propose_algebra(raw)
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('algebra',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.AlgebraSourceRecheck.v1')
            lean=base/'out/ReifiedAlgebra.lean'
            text=lean.read_text()
            changed=text.replace('def ell : ℚ := (-1 : ℚ)','def ell : ℚ := (-2 : ℚ)',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('algebra',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'ALGEBRA_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
