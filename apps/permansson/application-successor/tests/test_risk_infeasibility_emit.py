"""Source-bound risk-cap infeasibility Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_risk_infeasibility_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.risk_infeasibility import propose_risk_infeasibility
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.risk_infeasibility_emit import FORMAT,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/risk_infeasibility.v1.json'


def fixture():
    raw=json.loads(EXAMPLE.read_text())
    return raw,propose_risk_infeasibility(raw)


class RiskInfeasibilityEmitTests(unittest.TestCase):
    def test_example_emits_bound_instance(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['theorem_names'],['options_exact','receipt_checked','min_risk','cap_infeasible'])
        self.assertIn('def rows : Fin 2 → RationalMarkovMatrix (1 * 2) := fun a => controlledMatrix input a',source)
        self.assertIn('def v : Fin (1 * 2) → ℚ := fun y => (if y = (0 : Fin 2) then ((1 : ℚ) / (4 : ℚ)) else (1 : ℚ))',source)
        self.assertIn('      ((((7 : ℚ) / (16 : ℚ)) : ℚ) : ℝ) ≤ riskMass rows μ risk π) ∧',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        for key,value in (('minimal_risk_probability','1/4'),('lean_status','PASS'),
                          ('farkas_ray',{'mass_multipliers':['1/2','1'],'risk_cap_multiplier':'1'})):
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
            result=check_family('risk-infeasibility',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.RiskInfeasibilitySourceRecheck.v1')
            lean=base/'out/ReifiedRiskInfeasibility.lean'
            text=lean.read_text()
            changed=text.replace('def cap : ℚ := ((1 : ℚ) / (4 : ℚ))','def cap : ℚ := ((1 : ℚ) / (8 : ℚ))',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('risk-infeasibility',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'RISK_INFEASIBILITY_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
