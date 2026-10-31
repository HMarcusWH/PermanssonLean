"""Source-bound finite metric contraction Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_metric_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.metric import propose_metric
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.metric_emit import FORMAT,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/metric.v1.json'


def fixture():
    raw=json.loads(EXAMPLE.read_text())
    return raw,propose_metric(raw)


class MetricEmitTests(unittest.TestCase):
    def test_contractive_receipt_emits_bound_instance(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['theorem_names'],['metric_checked','receipt_checked','row_contraction',
                                                'invariant_metric_bound','exact_invariant_transport'])
        self.assertIn('def Kt : RationalMarkovMatrix (2 * 2) := inducedMatrix pert',source)
        self.assertIn('def ρ : ℚ := ((1 : ℚ) / (2 : ℚ))',source)
        self.assertIn('def w : ℚ := ((1 : ℚ) / (6 : ℚ))',source)
        self.assertIn('instance : Fact (IsFiniteMetric dm) := ⟨metric_checked⟩',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_noncontractive_receipts_are_not_bound(self):
        raw=json.loads(EXAMPLE.read_text())
        for row in raw['baseline']['P']:
            row['weights']={x:('0' if x==row['x'] else '1') for x in row['weights']}
        receipt=propose_metric(raw)
        with self.assertRaises(AppError) as raised:
            emit_source(raw,receipt)
        self.assertEqual(raised.exception.code,'METRIC_REIFY_SCOPE')

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        for key,value in (('contraction_factor','1/3'),('defect','1/5'),('lean_status','PASS')):
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
            result=check_family('metric',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.MetricSourceRecheck.v1')
            lean=base/'out/ReifiedMetric.lean'
            text=lean.read_text()
            changed=text.replace('def δ : ℚ := ((1 : ℚ) / (4 : ℚ))','def δ : ℚ := ((1 : ℚ) / (5 : ℚ))',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('metric',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'METRIC_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
