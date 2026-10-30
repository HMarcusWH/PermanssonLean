"""Installed-boundary regressions for the typed one-step risk flow profile."""
from __future__ import annotations
from copy import deepcopy
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.package_data import resource_bytes,export_extended_resources
from permansson_app.schema_validate import validate_packaged_schema
from permansson_app.strict_json import strict_loads


def cli(*args):
    env=dict(os.environ)
    env['PYTHONPATH']=str(APP/'src')
    env['PYTHONDONTWRITEBYTECODE']='1'
    return subprocess.run([sys.executable,'-B','-m','permansson_app',*map(str,args)],
                          cwd=APP,env=env,capture_output=True,text=True,timeout=25)

class OneStepRiskCLI(unittest.TestCase):
    def test_packaged_schema_resource_and_full_export(self):
        raw=strict_loads(resource_bytes('examples/risk_occupancy.v1.json'))
        self.assertEqual(validate_packaged_schema('schemas/risk_occupancy.v1.schema.json',raw)['status'],'PASS')
        with tempfile.TemporaryDirectory() as td:
            names=export_extended_resources(Path(td)/'schemas')
            self.assertEqual(len(names),55)
            self.assertIn('schemas/risk_occupancy.v1.schema.json',names)
            self.assertIn('examples/risk_occupancy.v1.json',names)

    def test_cli_stores_checkable_numeric_report_with_unassessed_claims(self):
        with tempfile.TemporaryDirectory() as td:
            out=Path(td)/'result'
            p=cli('one-step-risk',APP/'src/permansson_app/data/examples/risk_occupancy.v1.json','--output',out)
            self.assertEqual(p.returncode,0,p.stderr)
            printed=json.loads(p.stdout)
            self.assertEqual(printed['numeric_status'],'PASS')
            receipt=json.loads((out/'occupancy_receipt.json').read_text())
            self.assertEqual(receipt['expected_terminal_reward'],'1/2')
            self.assertEqual(receipt['next_step_risk_probability'],'1/2')
            self.assertEqual(receipt['lean_status'],'NOT_EXECUTED')
            check=json.loads((out/'independent_check.json').read_text())
            self.assertEqual(check['status'],'PASS')
            self.assertEqual(check['primal_dual_status'],'OPTIMAL_VERIFIED')
            report=json.loads((out/'scientific_report.json').read_text())
            self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(len(report['scientific_certificate_dimensions']),9)
            self.assertEqual(report['capability'],'finite.one_step_risk_occupancy.numeric.v1')

    def test_unknown_or_extra_input_field_fails_before_output(self):
        raw=strict_loads(resource_bytes('examples/risk_occupancy.v1.json'))
        raw['release_approved']=True
        with tempfile.TemporaryDirectory() as td:
            path=Path(td)/'fake.json'
            path.write_text(json.dumps(raw))
            out=Path(td)/'out'
            p=cli('one-step-risk',path,'--output',out)
            self.assertEqual(p.returncode,2,p.stdout+p.stderr)
            self.assertIn('SCHEMA_INVALID',p.stderr)
            self.assertFalse(out.exists())

    def test_unprovable_infeasibility_is_not_called_proved(self):
        raw=strict_loads(resource_bytes('examples/risk_occupancy.v1.json'))
        raw['risk_cap']='0'
        for row in raw['model']['P']:
            if row['x']=='safe':row['weights']={'safe':'0','danger':'1'}
        with tempfile.TemporaryDirectory() as td:
            path=Path(td)/'infeasible.json';path.write_text(json.dumps(raw))
            out=Path(td)/'out'
            p=cli('one-step-risk',path,'--output',out)
            self.assertEqual(p.returncode,2,p.stdout+p.stderr)
            self.assertIn('RISK_NO_CERTIFICATE',p.stderr)
            self.assertFalse(out.exists())

    def test_output_must_be_fresh(self):
        with tempfile.TemporaryDirectory() as td:
            out=Path(td)/'already';out.mkdir()
            p=cli('one-step-risk',APP/'src/permansson_app/data/examples/risk_occupancy.v1.json','--output',out)
            self.assertEqual(p.returncode,2,p.stdout+p.stderr)
            self.assertIn('OUTPUT_SCOPE',p.stderr)

if __name__=='__main__':unittest.main()
