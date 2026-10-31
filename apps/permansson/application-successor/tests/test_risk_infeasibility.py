"""Exact one-step risk-cap infeasibility certificates: floors, Farkas ray, CLI and adversaries."""
from __future__ import annotations
import copy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.risk_infeasibility import propose_risk_infeasibility
from permansson_app.engines.risk_occupancy import propose_risk
from permansson_app.receipts.risk_infeasibility import check_risk_infeasibility

EXAMPLE=APP/'src/permansson_app/data/examples/risk_infeasibility.v1.json'
FEASIBLE=APP/'src/permansson_app/data/examples/risk_occupancy.v1.json'


def request(path=EXAMPLE):
    return json.loads(path.read_text())


def _cli(request_path,output):
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONPATH']=str(APP/'src')
    return subprocess.run([sys.executable,'-B','-m','permansson_app','one-step-risk-infeasibility',str(request_path),
                           '--output',str(output)],cwd=APP,env=env,text=True,capture_output=True,timeout=60)


class RiskInfeasibilityTests(unittest.TestCase):
    def test_example_certificate(self):
        raw=request();receipt=propose_risk_infeasibility(raw)
        self.assertEqual(check_risk_infeasibility(raw,receipt)['status'],'INFEASIBILITY_VERIFIED')
        self.assertEqual(receipt['state_risk_floors'],['1/4','1'])
        self.assertEqual(receipt['floor_actions'],[['stay'],['stay','gamble']])
        self.assertEqual((receipt['minimal_risk_probability'],receipt['cap_shortfall']),('7/16','3/16'))
        self.assertEqual(receipt['farkas_ray'],{'mass_multipliers':['1/4','1'],'risk_cap_multiplier':'1'})

    def test_optimum_route_still_makes_no_infeasibility_claim(self):
        # The bounded LP generator of `one-step-risk` never presents a failed search as a proof.
        with self.assertRaises(AppError) as raised:propose_risk(request())
        self.assertEqual(raised.exception.code,'RISK_NO_CERTIFICATE')

    def test_generated_lp_coefficients_beyond_the_input_precision(self):
        # Every action keeps danger mass 1/2^200, so the least risk is 1/2^200;
        # a cap of 1/2^201 is infeasible. The danger reward 1/3^100 makes the
        # shared generated LP's objective coefficients exceed 256 bits.
        from fractions import Fraction
        from permansson_app.identity import rational_text
        raw=request()
        p=Fraction(1,2**200)
        for row in raw['model']['P']:
            row['weights']={'danger':rational_text(p),'safe':rational_text(1-p)}
        for row in raw['terminal_rewards']:
            row['value']='0' if row['state'][1]=='safe' else rational_text(Fraction(1,3**100))
        raw['risk_cap']=rational_text(p/2)
        receipt=propose_risk_infeasibility(raw)
        self.assertEqual(check_risk_infeasibility(raw,receipt)['status'],'INFEASIBILITY_VERIFIED')
        self.assertEqual(receipt['minimal_risk_probability'],rational_text(p))

    def test_feasible_caps_are_refused(self):
        raw=request();raw['risk_cap']='7/16'          # exactly the floor total: met by the floor policy
        with self.assertRaises(AppError) as raised:propose_risk_infeasibility(raw)
        self.assertEqual(raised.exception.code,'RISK_CAP_FEASIBLE')
        with self.assertRaises(AppError):propose_risk_infeasibility(request(FEASIBLE))

    def test_false_rays_and_tampering_rejected(self):
        raw=request();receipt=propose_risk_infeasibility(raw)
        cases=[('farkas_ray',{'mass_multipliers':['1/2','1'],'risk_cap_multiplier':'1'}),  # above stay's risk
               ('farkas_ray',{'mass_multipliers':['0','1'],'risk_cap_multiplier':'1'}),    # not attained
               ('farkas_ray',{'mass_multipliers':['1/4','1'],'risk_cap_multiplier':'2'}),
               ('minimal_risk_probability','1/2'),('floor_actions',[['stay'],['stay']]),
               ('status','RISK_CAP_FEASIBLE'),('lean_status','PASS')]
        for key,value in cases:
            bad=copy.deepcopy(receipt);bad[key]=value
            with self.subTest(key=key,value=value),self.assertRaises(AppError):check_risk_infeasibility(raw,bad)
        bad=copy.deepcopy(receipt);bad['extra']=1
        with self.assertRaises(AppError):check_risk_infeasibility(raw,bad)

    def test_receipt_for_a_looser_cap_rejected(self):
        raw=request();receipt=propose_risk_infeasibility(raw)
        loose=copy.deepcopy(raw);loose['risk_cap']='1/2'
        with self.assertRaises(AppError):check_risk_infeasibility(loose,receipt)

    def test_real_cli(self):
        with tempfile.TemporaryDirectory() as temp:
            output=Path(temp)/'run'
            p=_cli(EXAMPLE,output)
            self.assertEqual(p.returncode,0,p.stdout+p.stderr)
            check=json.loads((output/'independent_check.json').read_text())
            report=json.loads((output/'scientific_report.json').read_text())
            self.assertEqual(check['status'],'INFEASIBILITY_VERIFIED')
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
            p=_cli(FEASIBLE,Path(temp)/'feasible')
            self.assertEqual(p.returncode,2,p.stdout+p.stderr)
            self.assertEqual(json.loads(p.stderr)['error']['code'],'RISK_CAP_FEASIBLE')
            self.assertFalse((Path(temp)/'feasible').exists())


if __name__=='__main__':
    unittest.main()
