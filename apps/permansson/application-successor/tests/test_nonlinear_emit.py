"""Source-bound nonlinear classwise objective Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_nonlinear_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.nonlinear import propose_nonlinear
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.nonlinear_emit import FORMAT,emit_files,emit_source
from permansson_app.strict_json import MAX_BYTES
from permansson_app.identity import rational_text
from fractions import Fraction

EXAMPLE=APP/'src/permansson_app/data/examples/nonlinear.v1.json'
TWO_COPIES=APP/'tests/fixtures/nonlinear_two_copies.v1.json'


def fixture(path=EXAMPLE):
    raw=json.loads(path.read_text())
    return raw,propose_nonlinear(raw)


class NonlinearEmitTests(unittest.TestCase):
    def test_checked_receipt_emits_all_policies_and_optimum(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['policies'],4)
        self.assertEqual(meta['scope']['aggregation_order'],'EXPECTATION_OF_CLASSWISE_FUNCTIONAL')
        self.assertEqual(meta['theorem_names'],['options_exact','receipt_checked','stationary_optimum',
            'policy_value_0','policy_value_1','policy_value_2','policy_value_3'])
        self.assertIn('  boundControlSystem input options options_exact states_pos',source)
        self.assertIn('def tied : Finset (Fin (1 * 2) → Fin 2) := {(![1, 1] : Fin (1 * 2) → Fin 2)}',source)
        # stay/stay: two absorbing classes; the classwise expectation 1/2 is
        # not the functional of the expected descriptor (5/6).
        block=source.split('theorem policy_value_0 :',1)[1].split('theorem ',1)[0]
        self.assertIn('((((1 : ℚ) / (2 : ℚ)) : ℚ) : ℝ)',block)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_two_copy_fixture_has_unique_optimum(self):
        raw,receipt=fixture(TWO_COPIES)
        _,meta=emit_source(raw,receipt)
        self.assertEqual(meta['scope']['policies'],16)
        self.assertEqual(receipt['attaining_policy_indices'],[15])

    def test_results_beyond_the_input_precision_emit(self):
        # Inputs within the 256-bit input bound whose stationary laws need 398
        # bits: the emitter reads receipt values with the result-sized parser.
        raw=json.loads(EXAMPLE.read_text())
        stay={'left':{'left':'%d/%d'%(2**199+1,2**200),'right':'%d/%d'%(2**199-1,2**200)},
              'right':{'left':'%d/%d'%(2**199-3,2**200-1),'right':'%d/%d'%(2**199+2,2**200-1)}}
        for row in raw['model']['P']:
            if row['a']=='stay':row['weights']=stay[row['x']]
        receipt=propose_nonlinear(raw)
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['scope']['policies'],4)
        self.assertGreater(max(int(n).bit_length() for n in re.findall(r'\((\d+) : ℚ\)',source)),256)

    def test_receipts_larger_than_the_request_limit_are_read(self):
        # Codex's case: 16 stationary selectors with ~200-bit P rows give a
        # receipt far above the 128 KiB request limit; lean-emit and
        # lean-recheck read it with the result limit.
        raw=json.loads(TWO_COPIES.read_text())
        for k,row in enumerate(raw['model']['P']):
            dest=next(x for x,w in row['weights'].items() if w=='1')
            other=next(x for x in row['weights'] if x!=dest)
            e=Fraction(1,2**200-(2*k+1))
            row['weights']={dest:rational_text(1-e),other:rational_text(e)}
        for k,row in enumerate(raw['model']['U']):
            dest=next(s for s,w in row['weights'].items() if w=='1')
            other=next(s for s in row['weights'] if s!=dest)
            e=Fraction(1,2**199-(2*k+1))
            row['weights']={dest:rational_text(1-e),other:rational_text(e)}
        receipt=propose_nonlinear(raw)
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            self.assertLess((base/'request.json').stat().st_size,MAX_BYTES)
            self.assertGreater((base/'receipt.json').stat().st_size,MAX_BYTES)
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('nonlinear',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.NonlinearSourceRecheck.v1')
            # Requests keep the smaller limit.
            (base/'big_request.json').write_bytes(b' '*MAX_BYTES+json.dumps(raw).encode())
            with self.assertRaises(AppError) as raised:
                emit_files(base/'big_request.json',base/'receipt.json',base/'out2')
            self.assertEqual(raised.exception.code,'INPUT_SIZE')

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['policies'][0]['expected_classwise_score']='5/6';mutations.append(bad)
        bad=deepcopy(receipt);bad['attaining_policy_indices']=[2,3];mutations.append(bad)
        bad=deepcopy(receipt);bad['optimum_value']='1';mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['optimum_value']),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('nonlinear',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.NonlinearSourceRecheck.v1')
            lean=base/'out/ReifiedNonlinear.lean'
            text=lean.read_text()
            changed=text.replace('def optimum : ℚ := ((5 : ℚ) / (6 : ℚ))','def optimum : ℚ := (1 : ℚ)',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('nonlinear',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'NONLINEAR_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
