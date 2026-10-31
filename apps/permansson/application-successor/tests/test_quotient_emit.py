"""Source-bound typed quotient Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_quotient_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.quotients import propose_quotient
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.quotient_emit import FORMAT,MAX_HORIZON,emit_files,emit_source

FIXTURE=APP/'tests/fixtures/quotient_geometric_exit.v1.json'
PACKAGED=APP/'src/permansson_app/data/examples/quotient.v1.json'


def fixture(path=FIXTURE):
    raw=json.loads(path.read_text())
    return raw,propose_quotient(raw)


class QuotientEmitTests(unittest.TestCase):
    def test_checked_receipt_emits_lumpability_and_transport(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['profiles'],['baseline','keep_strategy'])
        self.assertEqual(meta['scope']['interpretation'],'EXACT_STRONG_LUMPABILITY_FINITE_HORIZON_TRANSPORT_ONLY')
        self.assertEqual(meta['theorem_names'],['member_0_held_fixed','member_0_alpha_held_fixed',
            'profile_0_checked','transport_0','value_0_0','value_0_2',
            'profile_1_checked','transport_1','value_1_0','value_1_2'])
        self.assertIn('def K_1 : RationalMarkovMatrix (2 * 2) := inducedMatrix member_0',source)
        block=source.split('theorem value_0_0 :',1)[1].split('theorem ',1)[0]
        self.assertIn('((((8 : ℚ) / (27 : ℚ)) : ℚ) : ℝ)',block)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_packaged_example_emits_three_profiles(self):
        raw,receipt=fixture(PACKAGED)
        _,meta=emit_source(raw,receipt)
        self.assertEqual(meta['scope']['profiles'],['baseline','alpha_all','update_state'])

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['profiles'][0]['coarse_kernel'][0]=['1/2','1/2'];mutations.append(bad)
        bad=deepcopy(receipt);bad['profiles'][0]['fine_values'][0]='1/3';mutations.append(bad)
        bad=deepcopy(receipt);bad['profiles'][1]['coarse_values'][0]='1';mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['profiles'][0]['fine_values']),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_scope_limit(self):
        raw,_=fixture()
        raw=dict(raw,horizon=MAX_HORIZON+1)
        with self.assertRaises(AppError) as raised:emit_source(raw,propose_quotient(raw))
        self.assertEqual(raised.exception.code,'QUOTIENT_REIFY_SCOPE')

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('quotient',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.QuotientSourceRecheck.v1')
            lean=base/'out/ReifiedQuotient.lean'
            text=lean.read_text()
            changed=text.replace('def horizon : ℕ := 3','def horizon : ℕ := 2',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('quotient',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'QUOTIENT_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
