"""Exact CQ-1 certificate transport: budgets, envelopes, scope, CLI and adversaries."""
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
from permansson_app.engines.cq1_transport import propose_cq1_transport
from permansson_app.package_data import resource_bytes
from permansson_app.receipts.cq1_transport import check_cq1_transport
from permansson_app.schema_validate import validate_packaged_schema

EXAMPLE=APP/'src/permansson_app/data/examples/cq1_transport.v1.json'


def request():
    return json.loads(EXAMPLE.read_text())


def _alpha(model,s,x,weights):
    for row in model['alpha']:
        if row['s']==s and row['x']==x:row['weights']=weights


class CQ1TransportTests(unittest.TestCase):
    def test_example_transports_with_exact_budgets(self):
        raw=request();receipt=propose_cq1_transport(raw)
        self.assertEqual(check_cq1_transport(raw,receipt)['status'],'PASS')
        self.assertEqual((receipt['delta_baseline'],receipt['delta_intervention']),('1/50','1/50'))
        self.assertEqual(receipt['envelope_baseline'],'99/2500')                 # 1 - (49/50)^2
        self.assertEqual(receipt['transported_margin'],'301/1250')              # 8/25 - 2 * 99/2500
        self.assertEqual(receipt['transported_eta'],'1099/2500')                # 2/5 + 99/2500
        self.assertEqual(receipt['transport_status'],'TRANSPORTED_FINITE_CONSTITUTIVE_CERTIFICATE')
        # The approximate pair's own values respect the transported bound.
        self.assertEqual(receipt['direct_approximate_check'],{'min_region_survival':'1681/2500','uniform_margin':'729/2500'})

    def test_identical_pair_transports_with_zero_budget(self):
        raw=request()
        raw['approximate']={'baseline':copy.deepcopy(raw['cq1']['baseline']),
                            'treated':copy.deepcopy(raw['cq1']['intervention']['treated'])}
        receipt=propose_cq1_transport(raw)
        self.assertEqual((receipt['delta_baseline'],receipt['envelope_intervention']),('0','0'))
        self.assertEqual(receipt['transported_margin'],receipt['cq1_receipt']['uniform_margin'])

    def test_large_budget_is_not_transported(self):
        raw=request()
        _alpha(raw['approximate']['baseline'],'alert','ok',{'hold':'0','push':'1'})
        receipt=propose_cq1_transport(raw)
        self.assertEqual(check_cq1_transport(raw,receipt)['status'],'PASS')
        self.assertEqual(receipt['transport_status'],'NOT_TRANSPORTED')
        self.assertEqual(receipt['failed_conditions'],['BUDGET_ENVELOPES_EXCEED_MARGIN'])

    def test_scope_requires_shared_P_and_declared_target(self):
        raw=request()
        raw['approximate']['baseline']['P'][0]['weights']={'ok':'1','bad':'0'}
        with self.assertRaises(AppError):propose_cq1_transport(raw)
        raw=request()
        row=raw['approximate']['treated']['U'][0]
        row['weights']={k:('0' if v=='1' else '1') if v in ('0','1') else v for k,v in row['weights'].items()}
        with self.assertRaises(AppError):propose_cq1_transport(raw)

    def test_uncertified_cq1_is_refused(self):
        raw=request();raw['cq1']['eta']='0'
        with self.assertRaises(AppError) as raised:propose_cq1_transport(raw)
        self.assertEqual(raised.exception.code,'CQ1_TRANSPORT_SCOPE')

    def test_tampered_receipts_rejected(self):
        raw=request();receipt=propose_cq1_transport(raw)
        for key,value in (('delta_baseline','1/100'),('transported_margin','8/25'),('transported_eta','2/5'),
                          ('transport_status','NOT_TRANSPORTED'),('budget_semantics','EMPIRICAL'),('lean_status','PASS')):
            bad=copy.deepcopy(receipt);bad[key]=value
            with self.subTest(key=key),self.assertRaises(AppError):check_cq1_transport(raw,bad)
        bad=copy.deepcopy(receipt);bad['cq1_receipt']['uniform_margin']='1/2'
        with self.assertRaises(AppError):check_cq1_transport(raw,bad)

    def test_schema_and_real_cli(self):
        doc=json.loads(resource_bytes('examples/cq1_transport.v1.json'))
        self.assertEqual(validate_packaged_schema('schemas/cq1_transport.v1.schema.json',doc)['status'],'PASS')
        doc['approximate']['extra']=1
        with self.assertRaises(AppError):validate_packaged_schema('schemas/cq1_transport.v1.schema.json',doc)
        env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONPATH']=str(APP/'src')
        with tempfile.TemporaryDirectory() as temp:
            out=Path(temp)/'run'
            p=subprocess.run([sys.executable,'-B','-m','permansson_app','finite-cq1-transport',str(EXAMPLE),'--output',str(out)],
                             cwd=APP,env=env,text=True,capture_output=True,timeout=60)
            self.assertEqual(p.returncode,0,p.stdout+p.stderr)
            self.assertEqual(json.loads(p.stdout)['transport_status'],'TRANSPORTED_FINITE_CONSTITUTIVE_CERTIFICATE')
            report=json.loads((out/'scientific_report.json').read_text())
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')


if __name__=='__main__':
    unittest.main()
