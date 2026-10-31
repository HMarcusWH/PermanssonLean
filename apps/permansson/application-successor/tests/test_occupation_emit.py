"""Source-bound finite occupation Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_occupation_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.occupation import compute_occupation
from permansson_app.errors import AppError
from permansson_app.finite_world import parse_finite_world
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.occupation_emit import FORMAT,emit_files,emit_source

FIXTURE=APP/'tests/fixtures/occupation_transient_split.v1.json'


def fixture():
    raw=json.loads(FIXTURE.read_text())
    return raw,compute_occupation(parse_finite_world(raw))


class OccupationEmitTests(unittest.TestCase):
    def test_checked_receipt_emits_classes_absorption_laws_and_mixture(self):
        raw,receipt=fixture()
        self.assertEqual(receipt['bottom_classes'],[[1,2],[3]])
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['bottom_classes'],2)
        self.assertEqual(meta['scope']['not_claimed'],['gr_pr_recovery','c10_original_margin'])
        names=meta['theorem_names']
        self.assertEqual(names[:3],['receipt_checked','dirichlet_checked','classes_exact'])
        self.assertEqual(names[-3:],['occupation_limit','random_limit_law','mean_mixture'])
        self.assertIn('random_limit_on_class_1',names)
        self.assertEqual(sum(n.startswith('absorption_') for n in names),8)
        self.assertIn('def K : RationalMarkovMatrix (2 * 2) := inducedMatrix input',source)
        self.assertIn('def class_0 : Finset (Fin (2 * 2)) := ({1, 2} : Finset (Fin 4))',source)
        self.assertIn('theorem receipt_checked : checkJointClassReceipt K cert laws mean = true := by',source)
        self.assertIn('  random_limit_law_eq_receipt K cert laws mean receipt_checked',source)
        # The transient state splits evenly between the two bottom classes.
        block=source.split('theorem absorption_0_0 :',1)[1].split('theorem ',1)[0]
        self.assertIn('((((1 : ℚ) / (2 : ℚ)) : ℚ) : ℝ)',block)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['absorption_weights'][0]=['1/3','2/3'];mutations.append(bad)
        bad=deepcopy(receipt);bad['bottom_classes']=[[1,2]];mutations.append(bad)
        bad=deepcopy(receipt);bad['stationary_laws'][0]=['1/3','2/3'];mutations.append(bad)
        bad=deepcopy(receipt);bad['expected_limit_laws'][0]=['0','1/2','0','1/2'];mutations.append(bad)
        bad=deepcopy(receipt);bad['limit_interpretation']='MEAN_LAW';mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['bottom_classes']),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_foreign_model_never_emits(self):
        raw,receipt=fixture()
        other=deepcopy(raw)
        other['P'][0]['weights']={'x0':'2/3','x1':'1/3'}
        with self.assertRaises(AppError):
            emit_source(other,receipt)

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'model.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'model.json',base/'receipt.json',base/'out')
            result=check_family('occupation',base/'model.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.OccupationSourceRecheck.v1')
            self.assertEqual(result['status'],'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF')
            lean=base/'out/ReifiedOccupation.lean'
            text=lean.read_text()
            changed=text.replace('  classes := {class_0, class_1}','  classes := {class_0}',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('occupation',base/'model.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'OCCUPATION_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
