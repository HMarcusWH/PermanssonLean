"""Source-bound rectangular-vs-committed nature Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_robust_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.robust_nature import propose_nature
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.robust_emit import FORMAT,MAX_HORIZON,emit_files,emit_source

FIXTURE=APP/'tests/fixtures/robust_nature_two_models.v1.json'
PACKAGED=APP/'src/permansson_app/data/examples/robust_nature.v1.json'


def fixture(path=FIXTURE,**changes):
    raw=dict(json.loads(path.read_text()),**changes)
    return raw,propose_nature(raw)


class RobustEmitTests(unittest.TestCase):
    def test_checked_receipt_emits_three_games_and_saddles(self):
        raw,receipt=fixture()
        self.assertEqual(receipt['comparison']['fixed_rectangular_minus_committed'],['0','-1/4'])
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['nature_models'],['theta1','theta2'])
        names=meta['theorem_names']
        for name in ('nature_0_held_fixed','game_checked','fixed_checked','committed_1_checked',
                     'rectangular_optimum_0','fixed_rectangular_1','committed_1_1','rectangular_le_committed'):
            self.assertIn(name,names)
        block=source.split('theorem rectangular_optimum_0 :',1)[1].split('theorem ',1)[0]
        self.assertIn('((((4 : ℚ) / (9 : ℚ)) : ℚ) : ℝ)',block)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_packaged_four_world_example_exceeds_reflection_bound(self):
        raw,receipt=fixture(PACKAGED)
        with self.assertRaises(AppError) as raised:emit_source(raw,receipt)
        self.assertEqual(raised.exception.code,'REIFICATION_SCOPE')

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['rectangular_optimal_values_by_remaining'][2][0]='1/2';mutations.append(bad)
        bad=deepcopy(receipt);bad['fixed_policy_rectangular_values_by_remaining'][2][1]='1/2';mutations.append(bad)
        bad=deepcopy(receipt);bad['fixed_policy_committed_values_by_nature'].reverse();mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['nature_ids']),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_scope_limit(self):
        raw,receipt=fixture(horizon=MAX_HORIZON+1)
        with self.assertRaises(AppError) as raised:emit_source(raw,receipt)
        self.assertEqual(raised.exception.code,'ROBUST_REIFY_SCOPE')

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('robust-nature',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.RobustNatureSourceRecheck.v1')
            lean=base/'out/ReifiedRobustNature.lean'
            text=lean.read_text()
            changed=text.replace('def horizon : ℕ := 2','def horizon : ℕ := 1',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('robust-nature',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'ROBUST_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
