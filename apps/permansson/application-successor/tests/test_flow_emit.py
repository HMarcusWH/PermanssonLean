"""Source-bound one-step risk-occupancy (flow) Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_flow_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.risk_occupancy import propose_risk
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.flow_emit import FORMAT,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/risk_occupancy.v1.json'


def fixture(**changes):
    raw=dict(json.loads(EXAMPLE.read_text()),**changes)
    return raw,propose_risk(raw)


class FlowEmitTests(unittest.TestCase):
    def test_checked_receipt_emits_dual_policy_and_reconstruction(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['optimization'],'ONE_TRANSITION_ALL_ADMISSIBLE_REAL_RANDOMIZED_MARKOV_POLICIES')
        self.assertEqual(meta['theorem_names'],['options_exact','receipt_checked','risk_optimum',
            'policy_held_fixed','policy_update_held_fixed','policy_rows','next_state_law_actual',
            'next_state_mass_0','next_state_mass_1'])
        self.assertIn('def rows : Fin 2 → RationalMarkovMatrix (1 * 2) := fun a => controlledMatrix input a',source)
        self.assertIn('def lam : ℚ := (1 : ℚ)',source)
        self.assertIn('def D : ℚ := ((1 : ℚ) / (2 : ℚ))',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_bound_duals_are_mapped_when_cap_is_slack(self):
        raw,receipt=fixture(risk_cap='1')
        source,_=emit_source(raw,receipt)
        self.assertIn('def lam : ℚ := (0 : ℚ)',source)
        self.assertIn('def wB : Fin (1 * 2) → Fin 2 → ℚ := fun y a => (if y = (0 : Fin 2) then '
                      '(if a = (0 : Fin 2) then (0 : ℚ) else (1 : ℚ))',source)

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['expected_terminal_reward']='1';mutations.append(bad)
        bad=deepcopy(receipt);bad['policy'][0]['action_weights']={'stay':'1','gamble':'0'};mutations.append(bad)
        bad=deepcopy(receipt);bad['lp_certificate']['primal']=['0','1','0','0'];mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['expected_terminal_reward']),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('flow',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.FlowSourceRecheck.v1')
            lean=base/'out/ReifiedFlow.lean'
            text=lean.read_text()
            changed=text.replace('def lam : ℚ := (1 : ℚ)','def lam : ℚ := (0 : ℚ)',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('flow',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'FLOW_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
