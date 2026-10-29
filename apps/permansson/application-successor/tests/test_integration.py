"""Actual CLI, source-preservation, legacy contract and schema integration."""
from __future__ import annotations
import hashlib,json,os
from pathlib import Path
import subprocess,sys,tempfile,unittest
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.errors import AppError
from permansson_app.legacy import validate_legacy
from permansson_app.process import RunBudget,run_bounded
from permansson_app.report import numeric_application_report,DIMENSIONS
from permansson_app.package_data import export_extended_resources,resource_bytes
from permansson_app.schema_validate import validate_packaged_schema
from permansson_app.strict_json import strict_loads
ROOT=Path(os.environ.get('PERMANSSON_SOURCE_ROOT',APP.parents[2])).resolve()


def command(*args):
 env=os.environ.copy();env['PYTHONPATH']=str(APP/'src');env['PYTHONDONTWRITEBYTECODE']='1'
 return subprocess.run([sys.executable,'-B','-m','permansson_app',*map(str,args)],
                       cwd=ROOT,env=env,text=True,capture_output=True,timeout=60)


class PackagedResourceTests(unittest.TestCase):
 def test_new_resources_in_wheel_compatible_path(self):
  with tempfile.TemporaryDirectory() as temp:
   d=Path(temp)/'new'
   hashes=export_extended_resources(d)
   self.assertEqual(len(hashes),22)
   for k,v in hashes.items():
    self.assertEqual(hashlib.sha256((d/k).read_bytes()).hexdigest(),v)
 def test_schema_finite(self):
  v=strict_loads(resource_bytes('examples/finite_world.v1.model.json'))
  self.assertEqual(validate_packaged_schema('schemas/finite_world.v1.schema.json',v)['status'],'PASS')
 def test_schema_lp(self):
  v=strict_loads(resource_bytes('examples/lp.v1.model.json'))
  self.assertEqual(validate_packaged_schema('schemas/lp.v1.schema.json',v)['status'],'PASS')
 def test_schema_reject_extra(self):
  v=strict_loads(resource_bytes('examples/lp.v1.model.json'))
  v['unexpected']=1
  with self.assertRaises(AppError):validate_packaged_schema('schemas/lp.v1.schema.json',v)
 def test_unknown_schema(self):
  with self.assertRaises(AppError):validate_packaged_schema('schemas/not-in-package.json',{})

class CLITests(unittest.TestCase):
 def test_finite_kernel_end_to_end(self):
  with tempfile.TemporaryDirectory() as temp:
   out=Path(temp)/'finite'
   p=command('finite-kernel',APP/'src/permansson_app/data/examples/finite_world.v1.model.json','--output',out)
   self.assertEqual(p.returncode,0,p.stderr)
   receipt=json.loads((out/'induced_kernel_receipt.json').read_text())
   check=json.loads((out/'independent_check.json').read_text())
   report=json.loads((out/'scientific_report.json').read_text())
   self.assertEqual(check['status'],'PASS')
   self.assertEqual(receipt['lean_status'],'NOT_EXECUTED')
   self.assertFalse(report['scientific_claims_verified'])
   self.assertEqual(set(report['scientific_certificate_dimensions']),set(DIMENSIONS))
 def test_lp_propose_end_to_end(self):
  with tempfile.TemporaryDirectory() as temp:
   out=Path(temp)/'lp'
   p=command('lp-propose',APP/'src/permansson_app/data/examples/lp.v1.model.json','--output',out)
   self.assertEqual(p.returncode,0,p.stderr)
   self.assertEqual(json.loads((out/'proposal.json').read_text())['status'],'CHECKED_OPTIMAL_CANDIDATE')
   self.assertEqual(json.loads((out/'independent_check.json').read_text())['status'],'OPTIMAL_VERIFIED')
 def test_lp_check_independent(self):
  with tempfile.TemporaryDirectory() as temp:
   root=Path(temp)
   p=command('lp-propose',APP/'src/permansson_app/data/examples/lp.v1.model.json','--output',root/'propose')
   self.assertEqual(p.returncode,0,p.stderr)
   receipt=json.loads((root/'propose/proposal.json').read_text())['receipt']
   (root/'receipt.json').write_text(json.dumps(receipt))
   q=command('lp-check',APP/'src/permansson_app/data/examples/lp.v1.model.json',root/'receipt.json','--output',root/'verify')
   self.assertEqual(q.returncode,0,q.stderr)
   self.assertEqual(json.loads((root/'verify/independent_check.json').read_text())['status'],'OPTIMAL_VERIFIED')
 def test_bad_model_no_success(self):
  with tempfile.TemporaryDirectory() as temp:
   root=Path(temp)
   (root/'bad.json').write_text('{"format":"fake"}')
   p=command('finite-kernel',root/'bad.json','--output',root/'out')
   self.assertEqual(p.returncode,2,p.stdout)
   self.assertFalse((root/'out').exists())
 def test_existing_output_rejected(self):
  with tempfile.TemporaryDirectory() as temp:
   d=Path(temp)/'existing';d.mkdir()
   p=command('lp-propose',APP/'src/permansson_app/data/examples/lp.v1.model.json','--output',d)
   self.assertEqual(p.returncode,2,p.stdout)
 def test_resource_cli_full(self):
  with tempfile.TemporaryDirectory() as temp:
   p=command('resources','--full','--output',Path(temp)/'out')
   self.assertEqual(p.returncode,0,p.stderr)
   self.assertTrue((Path(temp)/'out/schemas/lp.v1.schema.json').is_file())

class LegacyTests(unittest.TestCase):
 @classmethod
 def setUpClass(cls):
  if not (ROOT/'application/validator/validate_application.py').is_file():
   raise unittest.SkipTest('legacy repository source unavailable')
 def test_original_seven_fixtures(self):
  fixtures=json.loads((ROOT/'application/examples/expectations.json').read_text())
  with tempfile.TemporaryDirectory() as temp:
   for i,(name,errors) in enumerate(fixtures.items()):
    with self.subTest(fixture=name):
     result=validate_legacy(ROOT/f'application/examples/{name}/application.json',ROOT,Path(temp)/f'out{i}')
     actual=[e['code'] for e in result['original_result']['errors']]
     self.assertEqual(actual,errors)
     self.assertEqual(result['original_result']['contract_valid'],not bool(errors))
     self.assertFalse(result['scientific_claims_verified'])
 def test_source_pin_fails_closed(self):
  with tempfile.TemporaryDirectory() as temp:
   root=Path(temp);(root/'application/validator').mkdir(parents=True)
   (root/'application/validator/validate_application.py').write_text('print("false")')
   with self.assertRaises(AppError):
    validate_legacy(ROOT/'application/examples/grounded_pr_minimal/application.json',root,root/'out')

class BudgetTests(unittest.TestCase):
 def test_shared_output_budget(self):
  with tempfile.TemporaryDirectory() as temp:
   b=RunBudget.start(output_bytes=10,seconds=10);root=Path(temp)
   run_bounded([sys.executable,'-c',"print('ab')"],root,root/'a.log',budget=b)
   self.assertLess(b.remaining_output,10)
   with self.assertRaises(AppError):
    run_bounded([sys.executable,'-c',"print('abcdefghij')"],root,root/'b.log',budget=b)
 def test_legacy_exit_one_allowed(self):
  with tempfile.TemporaryDirectory() as temp:
   root=Path(temp)
   v=run_bounded([sys.executable,'-c','raise SystemExit(1)'],root,root/'log',allowed_exit_codes=(0,1))
   self.assertEqual(v['exit_code'],1)
 def test_global_deadline(self):
  with tempfile.TemporaryDirectory() as temp:
   b=RunBudget.start(seconds=.02);root=Path(temp)
   with self.assertRaises(AppError) as cm:
    run_bounded([sys.executable,'-c','import time;time.sleep(1)'],root,root/'log',budget=b,timeout=5)
   self.assertEqual(cm.exception.code,'PROCESS_TIMEOUT')

class ReportsTests(unittest.TestCase):
 def test_no_scientific_promotion(self):
  v=numeric_application_report(capability='f',model_semantic_identity={'sha256':'a'},
     computation_receipt={'a':1},independent_check={'status':'PASS'})
  self.assertEqual(len(v['scientific_certificate_dimensions']),9)
  self.assertIsNone(v['scientific_certificate_dimensions']['validity'])
  self.assertEqual(v['empirical_identification'],'NOT_IDENTIFIED')
 def test_unverified_checker_cannot_issue_report(self):
  with self.assertRaises(AppError):
   numeric_application_report(capability='f',model_semantic_identity={'sha256':'a'},
        computation_receipt={'a':1},independent_check={'status':'PENDING'})

if __name__=='__main__':unittest.main()
