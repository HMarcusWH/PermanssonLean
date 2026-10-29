"""End-to-end source/wheel compatible nature-chronology gate."""
from __future__ import annotations
import copy
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
REQUEST=APP/'src/permansson_app/data/examples/robust_nature.v1.json'

class NatureCLI(unittest.TestCase):
    def test_schema_accepts_complete_example(self):
        doc=json.loads(resource_bytes('examples/robust_nature.v1.json'))
        self.assertEqual(validate_packaged_schema('schemas/robust_nature.v1.schema.json',doc)['status'],'PASS')

    def test_schema_rejects_bad_physical_payload(self):
        doc=json.loads(resource_bytes('examples/robust_nature.v1.json'))
        doc['nature_models'][0]['P'][0]['weights']['mid']=False
        with self.assertRaises(AppError):validate_packaged_schema('schemas/robust_nature.v1.schema.json',doc)

    def test_real_cli(self):
        with tempfile.TemporaryDirectory() as temp:
            output=Path(temp)/'run'
            env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONPATH']=str(APP/'src')
            p=subprocess.run([sys.executable,'-B','-m','permansson_app','finite-robust-nature',str(REQUEST),'--output',str(output)],
                             cwd=APP,env=env,text=True,capture_output=True,timeout=30)
            self.assertEqual(p.returncode,0,p.stdout+p.stderr)
            check=json.loads((output/'independent_check.json').read_text())
            report=json.loads((output/'scientific_report.json').read_text())
            self.assertEqual(check['status'],'PASS')
            self.assertTrue(all(v is None for v in report['scientific_certificate_dimensions'].values()))
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
            self.assertEqual(json.loads((output/'nature_receipt.json').read_text())['comparison']['fixed_rectangular_minus_committed'][0],'-1')

    def test_failure_does_not_create_output_directory(self):
        with tempfile.TemporaryDirectory() as temp:
            bad=Path(temp)/'bad.json';doc=json.loads(REQUEST.read_text());doc['horizon']=13
            bad.write_text(json.dumps(doc));output=Path(temp)/'failed'
            env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONPATH']=str(APP/'src')
            p=subprocess.run([sys.executable,'-B','-m','permansson_app','finite-robust-nature',str(bad),'--output',str(output)],
                             cwd=APP,env=env,text=True,capture_output=True,timeout=30)
            self.assertEqual(p.returncode,2,p.stdout+p.stderr)
            self.assertFalse(output.exists())
            self.assertFalse(json.loads(p.stderr)['ok'])

if __name__=='__main__':unittest.main()
