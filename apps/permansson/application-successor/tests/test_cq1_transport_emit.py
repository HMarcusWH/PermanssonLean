"""Source-bound CQ-1 transport Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_cq1_transport_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.cq1_transport import propose_cq1_transport
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.cq1_transport_emit import FORMAT,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/cq1_transport.v1.json'


def fixture():
    raw=json.loads(EXAMPLE.read_text())
    return raw,propose_cq1_transport(raw)


class CQ1TransportEmitTests(unittest.TestCase):
    def test_example_emits_bound_instance(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['theorem_names'],['treated_held_fixed','approxBase_held_fixed','approxTreated_held_fixed',
                                                'receipt_checked','transport_checked','transported_certificate'])
        self.assertIn('def δ₀ : ℚ := ((1 : ℚ) / (50 : ℚ))',source)
        self.assertIn('theorem transport_checked : checkTransport K₀ K₁ A₀ A₁ 2 κ δ₀ δJ = true := by',source)
        self.assertIn('        ((((301 : ℚ) / (1250 : ℚ)) : ℚ) : ℝ) := by',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_untransported_receipts_are_not_bound(self):
        raw,_=fixture()
        for row in raw['approximate']['baseline']['alpha']:
            if row['s']=='alert' and row['x']=='ok':row['weights']={'hold':'0','push':'1'}
        receipt=propose_cq1_transport(raw)
        with self.assertRaises(AppError) as raised:emit_source(raw,receipt)
        self.assertEqual(raised.exception.code,'CQ1_TRANSPORT_REIFY_SCOPE')

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        for key,value in (('transported_margin','8/25'),('delta_intervention','0'),('lean_status','PASS')):
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
            result=check_family('cq1-transport',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.CQ1TransportSourceRecheck.v1')
            lean=base/'out/ReifiedCQ1Transport.lean'
            text=lean.read_text()
            changed=text.replace('def δJ : ℚ := ((1 : ℚ) / (50 : ℚ))','def δJ : ℚ := ((1 : ℚ) / (40 : ℚ))',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('cq1-transport',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'CQ1_TRANSPORT_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
