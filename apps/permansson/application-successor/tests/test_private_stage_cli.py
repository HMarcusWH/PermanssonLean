"""End-to-end source/wheel compatible private-stage saddle gate."""
from __future__ import annotations
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.package_data import resource_bytes
from permansson_app.schema_validate import validate_packaged_schema
from permansson_app.errors import AppError

APP=Path(__file__).resolve().parents[1]
REQUEST=APP/'src/permansson_app/data/examples/private_stage.v1.json'


def _run(request,output):
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONPATH']=str(APP/'src')
    return subprocess.run([sys.executable,'-B','-m','permansson_app','finite-private-stage',str(request),'--output',str(output)],
                          cwd=APP,env=env,text=True,capture_output=True,timeout=60)


class PrivateStageCLI(unittest.TestCase):
    def test_schema_accepts_example(self):
        doc=json.loads(resource_bytes('examples/private_stage.v1.json'))
        self.assertEqual(validate_packaged_schema('schemas/private_stage.v1.schema.json',doc)['status'],'PASS')

    def test_schema_rejects_fifth_control_and_decimal(self):
        doc=json.loads(resource_bytes('examples/private_stage.v1.json'))
        doc['labels']['controls']+=['a','b']
        with self.assertRaises(AppError):validate_packaged_schema('schemas/private_stage.v1.schema.json',doc)
        doc=json.loads(resource_bytes('examples/private_stage.v1.json'))
        doc['payoff'][0][0]='0.5'
        with self.assertRaises(AppError):validate_packaged_schema('schemas/private_stage.v1.schema.json',doc)

    def test_real_cli(self):
        with tempfile.TemporaryDirectory() as temp:
            output=Path(temp)/'run'
            p=_run(REQUEST,output)
            self.assertEqual(p.returncode,0,p.stdout+p.stderr)
            check=json.loads((output/'independent_check.json').read_text())
            report=json.loads((output/'scientific_report.json').read_text())
            self.assertEqual(check['status'],'PASS')
            self.assertEqual(check['saddle_certificate'],'BOTH_SIDES_CHECKED')
            self.assertTrue(all(v is None for v in report['scientific_certificate_dimensions'].values()))
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
            self.assertEqual(json.loads((output/'private_stage_receipt.json').read_text())['value'],'1')

    def test_failure_does_not_create_output_directory(self):
        with tempfile.TemporaryDirectory() as temp:
            bad=Path(temp)/'bad.json';doc=json.loads(REQUEST.read_text());doc['payoff'][1].pop()
            bad.write_text(json.dumps(doc));output=Path(temp)/'failed'
            p=_run(bad,output)
            self.assertEqual(p.returncode,2,p.stdout+p.stderr)
            self.assertFalse(output.exists())
            self.assertFalse(json.loads(p.stderr)['ok'])


if __name__=='__main__':
    unittest.main()
