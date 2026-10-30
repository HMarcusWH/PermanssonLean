"""Source-bound killed-kernel survival Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_survival_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.finite_survival import propose_finite_survival
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.survival_emit import FORMAT,MAX_HORIZON,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/finite_survival.v1.json'


def fixture():
    raw=json.loads(EXAMPLE.read_text())
    return raw,propose_finite_survival(raw)


class SurvivalEmitTests(unittest.TestCase):
    def test_checked_comparison_emits_tables_effects_and_held_fixed(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['interpretation'],'FINITE_HORIZON_DIAGNOSTIC_ONLY')
        self.assertEqual(meta['theorem_names'],['treated_held_fixed','treated_update_held_fixed',
            'baseline_table_checked','treated_table_checked','horizon_effect_0','horizon_effect_2'])
        self.assertIn('checkSurvivalTable (inducedMatrix base) region horizon baselineTable = true',source)
        self.assertIn('checkSurvivalTable (inducedMatrix treated) region horizon treatedTable = true',source)
        # Effects are baseline minus treated at the horizon: 1/4 - 1 = -3/4.
        self.assertIn('= ((((-3 : ℚ) / (4 : ℚ)) : ℚ) : ℝ)',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['baseline_survival'][1][0]='1/3';mutations.append(bad)
        bad=deepcopy(receipt);bad['finite_effect_signs']=['positive','negative'];mutations.append(bad)
        bad=deepcopy(receipt);bad['minimum_abs_effect']='1/2';mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['finite_effect_signs']),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_scope_limits(self):
        raw,_=fixture()
        raw=dict(raw,horizon=MAX_HORIZON+1)
        with self.assertRaises(AppError) as raised:emit_source(raw,propose_finite_survival(raw))
        self.assertEqual(raised.exception.code,'SURVIVAL_REIFY_SCOPE')

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('survival',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.SurvivalSourceRecheck.v1')
            lean=base/'out/ReifiedSurvival.lean'
            lean.write_text(lean.read_text().replace('def horizon : ℕ := 2','def horizon : ℕ := 1',1))
            with self.assertRaises(AppError) as raised:
                check_family('survival',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'SURVIVAL_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
