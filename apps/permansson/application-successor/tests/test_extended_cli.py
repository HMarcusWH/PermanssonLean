"""New installed-style CLI paths, schema resources, independent evidence and errors."""
from __future__ import annotations
import json,os,subprocess,sys,tempfile
from pathlib import Path
import unittest
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.package_data import resource_bytes,export_extended_resources
from permansson_app.schema_validate import validate_packaged_schema
from permansson_app.strict_json import strict_loads
ROOT=Path(os.environ.get('PERMANSSON_SOURCE_ROOT',APP.parents[2])).resolve()

def cli(*args):
 env=dict(os.environ)
 env['PYTHONPATH']=str(APP/'src')
 env['PYTHONDONTWRITEBYTECODE']='1'
 return subprocess.run([sys.executable,'-B','-m','permansson_app',*map(str,args)],
                       cwd=ROOT,capture_output=True,text=True,timeout=40,env=env)

class ExtendedInstalledCLI(unittest.TestCase):
 def test_resources_are_packaged_and_schemas_validate(self):
  for kind in ('residence','nonlinear'):
   with self.subTest(kind=kind):
    schema=f'schemas/{kind}.v1.schema.json'
    data=strict_loads(resource_bytes(f'examples/{kind}.v1.json'))
    self.assertEqual(validate_packaged_schema(schema,data)['status'],'PASS')
  with tempfile.TemporaryDirectory() as temp:
   hashes=export_extended_resources(Path(temp)/'resources')
   self.assertTrue({'schemas/residence.v1.schema.json','schemas/nonlinear.v1.schema.json',
     'examples/residence.v1.json','examples/nonlinear.v1.json'}.issubset(hashes))
 def test_both_successful_cli_scopes(self):
  for kind,cmd,receipt in (('residence','finite-residence','residence_receipt.json'),
                           ('nonlinear','nonlinear-stationary','nonlinear_receipt.json')):
   with self.subTest(kind=kind),tempfile.TemporaryDirectory() as temp:
    root=Path(temp)
    out=root/'out'
    result=cli(cmd,APP/f'src/permansson_app/data/examples/{kind}.v1.json','--output',out)
    self.assertEqual(result.returncode,0,result.stderr)
    self.assertTrue(json.loads((out/receipt).read_text())['scientific_claims_verified'] is False)
    self.assertEqual(json.loads((out/'independent_check.json').read_text())['status'],'PASS')
    report=json.loads((out/'scientific_report.json').read_text())
    self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
    self.assertFalse(report['scientific_claims_verified'])
    self.assertEqual(len(report['scientific_certificate_dimensions']),9)
    self.assertEqual(json.loads(result.stdout)['numeric_status'],'PASS')
 def test_schema_reject_extra_field(self):
  for kind,cmd in (('residence','finite-residence'),('nonlinear','nonlinear-stationary')):
   with self.subTest(kind=kind),tempfile.TemporaryDirectory() as temp:
    root=Path(temp);data=json.loads(resource_bytes(f'examples/{kind}.v1.json'))
    data['claim_empirically_certified']=True
    (root/'bad.json').write_text(json.dumps(data))
    r=cli(cmd,root/'bad.json','--output',root/'out')
    self.assertEqual(r.returncode,2)
    self.assertIn('SCHEMA_INVALID',r.stderr)
    self.assertFalse((root/'out').exists())
 def test_existing_output_must_not_be_overwritten(self):
  with tempfile.TemporaryDirectory() as temp:
   root=Path(temp);(root/'out').mkdir()
   r=cli('nonlinear-stationary',APP/'src/permansson_app/data/examples/nonlinear.v1.json','--output',root/'out')
   self.assertEqual(r.returncode,2)
   self.assertIn('OUTPUT_SCOPE',r.stderr)

if __name__=='__main__':unittest.main()
