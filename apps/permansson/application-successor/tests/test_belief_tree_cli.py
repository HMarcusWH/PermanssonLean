"""End-to-end exact history-tree CLI, schema, source and status gates."""
from __future__ import annotations
from copy import deepcopy
from pathlib import Path
import hashlib,json,os,subprocess,sys,tempfile,unittest
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.package_data import resource_bytes,export_extended_resources
from permansson_app.schema_validate import validate_packaged_schema
from permansson_app.strict_json import strict_loads


def run(*args):
    env=dict(os.environ)
    env['PYTHONPATH']=str(APP/'src')
    env['PYTHONDONTWRITEBYTECODE']='1'
    return subprocess.run([sys.executable,'-B','-m','permansson_app',*map(str,args)],
        cwd=APP,env=env,capture_output=True,text=True,timeout=35)


class BeliefTreeCLI(unittest.TestCase):
 def test_schema_and_package_resources(self):
  raw=strict_loads(resource_bytes('examples/belief_tree.v1.json'))
  self.assertEqual(validate_packaged_schema('schemas/belief_tree.v1.schema.json',raw)['status'],'PASS')
  with tempfile.TemporaryDirectory() as temp:
   hashes=export_extended_resources(Path(temp)/'resources')
   for name in ('schemas/belief_tree.v1.schema.json','examples/belief_tree.v1.json'):
    self.assertEqual(hashes[name],hashlib.sha256((Path(temp)/'resources'/name).read_bytes()).hexdigest())

 def test_cli_computation_and_no_scientific_promotion(self):
  with tempfile.TemporaryDirectory() as temp:
   out=Path(temp)/'out'
   r=run('finite-belief-tree',APP/'src/permansson_app/data/examples/belief_tree.v1.json','--output',out)
   self.assertEqual(r.returncode,0,r.stdout+r.stderr)
   self.assertEqual(json.loads(r.stdout)['numeric_status'],'PASS')
   receipt=json.loads((out/'belief_tree_receipt.json').read_text())
   checker=json.loads((out/'independent_check.json').read_text())
   report=json.loads((out/'scientific_report.json').read_text())
   self.assertEqual(receipt['optimal_expected_terminal_reward'],'55/64')
   self.assertEqual(receipt['value_of_observation_history'],'7/64')
   self.assertEqual(checker['status'],'PASS')
   self.assertTrue(checker['terminal_law_from_actual_P_U'])
   self.assertEqual(report['capability'],'finite.observation_history_tree.numeric.v1')
   self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
   self.assertFalse(report['scientific_claims_verified'])
   self.assertEqual(len(report['scientific_certificate_dimensions']),9)

 def test_foreign_field_and_future_knowledge_claim_fails_before_output(self):
  raw=strict_loads(resource_bytes('examples/belief_tree.v1.json'))
  for field in ('future_hidden_state','scientific_claims_verified','authorization_granted'):
   with self.subTest(field=field),tempfile.TemporaryDirectory() as td:
    tampered=deepcopy(raw);tampered[field]=True
    inp=Path(td)/'bad.json';inp.write_text(json.dumps(tampered))
    out=Path(td)/'out'
    r=run('finite-belief-tree',inp,'--output',out)
    self.assertEqual(r.returncode,2,r.stdout+r.stderr)
    self.assertIn('SCHEMA_INVALID',r.stderr)
    self.assertFalse(out.exists())

 def test_invalid_likelihood_and_horizon_fail_without_output(self):
  raw=strict_loads(resource_bytes('examples/belief_tree.v1.json'))
  for change in ('likelihood','horizon'):
   with self.subTest(change=change),tempfile.TemporaryDirectory() as td:
    bad=deepcopy(raw)
    if change=='likelihood':bad['likelihoods'][0]['weights']['green']='1/2'
    else:bad['horizon']=4
    inp=Path(td)/'bad.json';inp.write_text(json.dumps(bad))
    out=Path(td)/'out';r=run('finite-belief-tree',inp,'--output',out)
    self.assertEqual(r.returncode,2,r.stdout+r.stderr)
    self.assertFalse(out.exists())

 def test_output_is_never_overwritten(self):
  with tempfile.TemporaryDirectory() as temp:
   out=Path(temp)/'existing';out.mkdir()
   r=run('finite-belief-tree',APP/'src/permansson_app/data/examples/belief_tree.v1.json','--output',out)
   self.assertEqual(r.returncode,2,r.stdout+r.stderr)
   self.assertIn('OUTPUT_SCOPE',r.stderr)

if __name__=='__main__':unittest.main()
