"""End-to-end CLI and package checks for bounded observation-only control."""
from __future__ import annotations
from pathlib import Path
import json,os,subprocess,sys,tempfile,unittest
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.package_data import resource_bytes,export_extended_resources
from permansson_app.strict_json import strict_loads
from permansson_app.schema_validate import validate_packaged_schema


def call(*args):
    env=dict(os.environ);env['PYTHONPATH']=str(APP/'src');env['PYTHONDONTWRITEBYTECODE']='1'
    return subprocess.run([sys.executable,'-B','-m','permansson_app',*map(str,args)],
                          cwd=APP,env=env,capture_output=True,text=True,timeout=25)

class BeliefCLI(unittest.TestCase):
    def test_installed_resources_and_strict_schema(self):
        x=strict_loads(resource_bytes('examples/belief.v1.json'))
        self.assertEqual(validate_packaged_schema('schemas/belief.v1.schema.json',x)['status'],'PASS')
        with tempfile.TemporaryDirectory() as td:
            d=export_extended_resources(Path(td)/'resources')
            self.assertEqual(len(d),48)
            self.assertIn('schemas/belief.v1.schema.json',d)
            self.assertIn('examples/belief.v1.json',d)

    def test_cli_observation_policy_and_nine_unassessed_dimensions(self):
        with tempfile.TemporaryDirectory() as td:
            out=Path(td)/'output'
            r=call('one-step-belief',APP/'src/permansson_app/data/examples/belief.v1.json','--output',out)
            self.assertEqual(r.returncode,0,r.stderr)
            self.assertEqual(json.loads(r.stdout)['numeric_status'],'PASS')
            receipt=json.loads((out/'belief_receipt.json').read_text())
            self.assertEqual(receipt['optimal_expected_terminal_reward'],'13/16')
            self.assertEqual(receipt['value_of_observation'],'1/16')
            self.assertEqual(receipt['policy'][2]['posterior'],None)
            checker=json.loads((out/'independent_check.json').read_text())
            self.assertEqual(checker['bounded_policies_exhaustively_checked'],4)
            self.assertEqual(checker['status'],'PASS')
            report=json.loads((out/'scientific_report.json').read_text())
            self.assertEqual(report['capability'],'finite.one_step_observation_belief.numeric.v1')
            self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(len(report['scientific_certificate_dimensions']),9)

    def test_false_approval_fails_schema_without_writing(self):
        x=strict_loads(resource_bytes('examples/belief.v1.json'))
        x['scientific_claims_verified']=True
        with tempfile.TemporaryDirectory() as td:
            f=Path(td)/'fake.json';f.write_text(json.dumps(x))
            out=Path(td)/'results'
            r=call('one-step-belief',f,'--output',out)
            self.assertEqual(r.returncode,2,r.stderr)
            self.assertIn('SCHEMA_INVALID',r.stderr)
            self.assertFalse(out.exists())

    def test_invalid_kernel_stochasticity_fails_without_output(self):
        x=strict_loads(resource_bytes('examples/belief.v1.json'))
        x['likelihoods'][0]['weights']['green']='1/4'
        with tempfile.TemporaryDirectory() as td:
            f=Path(td)/'fake.json';f.write_text(json.dumps(x))
            out=Path(td)/'results'
            r=call('one-step-belief',f,'--output',out)
            self.assertEqual(r.returncode,2,r.stderr)
            self.assertIn('BELIEF_INPUT',r.stderr)
            self.assertFalse(out.exists())

    def test_existing_output_cannot_be_overwritten(self):
        with tempfile.TemporaryDirectory() as td:
            out=Path(td)/'already_exists';out.mkdir()
            r=call('one-step-belief',APP/'src/permansson_app/data/examples/belief.v1.json','--output',out)
            self.assertEqual(r.returncode,2,r.stderr)
            self.assertIn('OUTPUT_SCOPE',r.stderr)

if __name__=='__main__':unittest.main()
