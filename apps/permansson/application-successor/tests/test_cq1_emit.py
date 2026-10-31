"""Source-bound CQ-1 finite certificate Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_cq1_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.cq1 import propose_cq1
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.cq1_emit import FORMAT,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/cq1.v1.json'


def fixture(**changes):
    raw=dict(json.loads(EXAMPLE.read_text()),**changes)
    return raw,propose_cq1(raw)


class CQ1EmitTests(unittest.TestCase):
    def test_certificate_receipt_emits_bound_instance(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['theorem_names'],['treated_held_fixed','treated_update_held_fixed',
            'receipt_checked','finite_constitutive_certificate','region_survival_0','region_survival_2',
            'baseline_property_0','intervened_property_0','baseline_property_2','intervened_property_2'])
        self.assertIn('def K₁ : RationalMarkovMatrix (2 * 2) := inducedMatrix treated',source)
        self.assertIn('def κ : ℚ := ((8 : ℚ) / (25 : ℚ))',source)
        self.assertIn('def η : ℚ := ((2 : ℚ) / (5 : ℚ))',source)
        self.assertIn('    checkCQ1 K₀ K₁ R basin B₁ Q 2 η κ (0 : Fin 4) (2 : Fin 4) = true := by',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_uncertified_receipts_are_not_bound(self):
        for change in ({'horizon':0},{'eta':'1/4'}):
            raw,receipt=fixture(**change)
            with self.subTest(change=change),self.assertRaises(AppError) as raised:
                emit_source(raw,receipt)
            self.assertEqual(raised.exception.code,'CQ1_REIFY_SCOPE')

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        for key,value in (('uniform_margin','39/100'),('min_region_survival','81/100'),('lean_status','PASS')):
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
            result=check_family('cq1',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.CQ1SourceRecheck.v1')
            lean=base/'out/ReifiedCQ1.lean'
            text=lean.read_text()
            changed=text.replace('def κ : ℚ := ((8 : ℚ) / (25 : ℚ))','def κ : ℚ := ((39 : ℚ) / (100 : ℚ))',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('cq1',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'CQ1_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
