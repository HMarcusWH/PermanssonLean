"""Full boundary/semantic-mutation tests for finite path TV perturbation."""
from __future__ import annotations
import copy,json,os,subprocess,sys,tempfile,unittest
from fractions import Fraction
from pathlib import Path
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.robustness import parse_perturbation,propose_perturbation
from permansson_app.receipts.robustness import check_perturbation
from permansson_app.schema_validate import validate_packaged_schema

class PerturbationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.example=APP/'src/permansson_app/data/examples/finite_perturbation.v1.json'
        cls.fixture=json.loads(cls.example.read_text())
    def setUp(self):
        self.raw=copy.deepcopy(self.fixture)
        self.problem=parse_perturbation(self.raw)
        self.receipt=propose_perturbation(self.problem)
    def check(self,raw=None,receipt=None):
        return check_perturbation(parse_perturbation(self.raw if raw is None else raw),self.receipt if receipt is None else receipt)
    def mutate(self,key,value):
        bad=copy.deepcopy(self.receipt);bad[key]=value
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_exact_scoped_values(self):
        r=self.receipt
        self.assertEqual(r['baseline_event_probability'],'9/16')
        self.assertEqual(r['alternative_event_probability'],'1')
        self.assertEqual(r['maximum_row_tv'],'1/4')
        self.assertEqual(r['initial_law_tv'],'0')
        self.assertEqual(r['bound_at_horizon'],'1/2')
        self.assertEqual(r['observed_abs_difference'],'7/16')
        self.assertEqual(self.check()['status'],'PASS')
    def test_example_schema_offline(self):
        self.assertEqual(validate_packaged_schema('schemas/finite_perturbation.v1.schema.json',self.raw)['status'],'PASS')
    def test_identity_model_exact(self):
        self.raw['alternative']=copy.deepcopy(self.raw['baseline'])
        p=parse_perturbation(self.raw);r=propose_perturbation(p)
        self.assertEqual(r['maximum_row_tv'],'0')
        self.assertEqual(r['observed_abs_difference'],'0')
        self.assertEqual(r['bound_at_horizon'],'0')
        self.assertEqual(check_perturbation(p,r)['status'],'PASS')
    def test_only_initial_distribution_differs(self):
        self.raw['alternative']=copy.deepcopy(self.raw['baseline'])
        self.raw['initial_alternative']=['0','0','1']
        p=parse_perturbation(self.raw);r=propose_perturbation(p)
        self.assertEqual(r['maximum_row_tv'],'0')
        self.assertEqual(r['initial_law_tv'],'1')
        self.assertEqual(r['bound_at_horizon'],'1')
        self.assertEqual(check_perturbation(p,r)['status'],'PASS')
    def test_horizon_zero_ignores_kernel_tv(self):
        self.raw['horizon']=0
        p=parse_perturbation(self.raw);r=propose_perturbation(p)
        self.assertEqual(r['bound_at_horizon'],'0')
        self.assertEqual(r['baseline_event_probability'],'1')
        self.assertEqual(r['alternative_event_probability'],'1')
        self.assertEqual(check_perturbation(p,r)['status'],'PASS')
    def test_one_step_values(self):
        self.raw['horizon']=1
        p=parse_perturbation(self.raw);r=propose_perturbation(p)
        self.assertEqual(r['baseline_event_probability'],'3/4')
        self.assertEqual(r['alternative_event_probability'],'1')
        self.assertEqual(r['bound_at_horizon'],'1/4')
        self.assertEqual(check_perturbation(p,r)['status'],'PASS')
    def test_max_horizon_accepted(self):
        self.raw['horizon']=32
        p=parse_perturbation(self.raw);r=propose_perturbation(p)
        self.assertEqual(r['bound_at_horizon'],'1')
        self.assertLess(Fraction(r['baseline_event_probability']),Fraction(1))
        self.assertEqual(check_perturbation(p,r)['status'],'PASS')
    def test_boolean_horizon_rejected(self):
        self.raw['horizon']=True
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_negative_horizon_rejected(self):
        self.raw['horizon']=-1
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_large_horizon_rejected(self):
        self.raw['horizon']=33
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_unaligned_state_names(self):
        self.raw['alternative']['states']['world'][0]='another'
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_unknown_region_pair(self):
        self.raw['region']=[['s0','foreign']]
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_duplicate_region(self):
        self.raw['region'].append(self.raw['region'][0])
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_empty_region(self):
        self.raw['region']=[]
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_invalid_initial_sum(self):
        self.raw['initial_baseline']=['1/2','0','0']
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_negative_initial_weight(self):
        self.raw['initial_baseline']=['3/2','-1/2','0']
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_missing_initial_mass(self):
        self.raw['initial_alternative']=['1','0']
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_bool_initial_weight(self):
        self.raw['initial_alternative'][0]=True
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_unregistered_input_extra_key(self):
        self.raw['unregistered']='x'
        with self.assertRaises(AppError):parse_perturbation(self.raw)
    def test_foreign_model_receipt(self):self.mutate('baseline_model_identity',{'sha256':'b'*64})
    def test_changed_comparison_identity(self):self.mutate('problem_semantic_identity',{'sha256':'a'*64})
    def test_changed_state_order(self):self.mutate('joint_states',list(reversed(self.receipt['joint_states'])))
    def test_forged_row_tv(self):self.mutate('row_total_variations',['0','0','0'])
    def test_forged_max_tv(self):self.mutate('maximum_row_tv','0')
    def test_forged_initial_tv(self):self.mutate('initial_law_tv','1')
    def test_forged_bound(self):self.mutate('bound_at_horizon','0')
    def test_changed_baseline_table(self):
        v=copy.deepcopy(self.receipt['baseline_survival_rows'])
        v[1][0]='1'
        self.mutate('baseline_survival_rows',v)
    def test_changed_alternative_table(self):
        v=copy.deepcopy(self.receipt['alternative_survival_rows'])
        v[2][0]='0'
        self.mutate('alternative_survival_rows',v)
    def test_missing_horizon_row(self):self.mutate('alternative_survival_rows',self.receipt['alternative_survival_rows'][:-1])
    def test_false_observed_difference(self):self.mutate('observed_abs_difference','1')
    def test_false_baseline_probability(self):self.mutate('baseline_event_probability','0')
    def test_forged_no_long_run_claim(self):self.mutate('no_long_run_claim',False)
    def test_forged_lean(self):self.mutate('lean_status','PASS')
    def test_forged_empirical(self):self.mutate('empirical_identification','POINT_IDENTIFIED')
    def test_forged_science(self):self.mutate('scientific_claims_verified',True)
    def test_extra_result_field(self):self.mutate('forged_review',True)
    def test_cli_and_no_scientific_promotion(self):
        with tempfile.TemporaryDirectory() as d:
            out=Path(d)/'out';env=dict(os.environ,PYTHONPATH=str(APP/'src'),PYTHONDONTWRITEBYTECODE='1')
            run=subprocess.run([sys.executable,'-B','-m','permansson_app','finite-perturbation',str(self.example),'--output',str(out)],
                cwd=APP,env=env,capture_output=True,text=True,timeout=30)
            self.assertEqual(run.returncode,0,run.stderr)
            self.assertEqual(json.loads((out/'independent_check.json').read_text())['status'],'PASS')
            report=json.loads((out/'scientific_report.json').read_text())
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(report['empirical_identification'],'NOT_IDENTIFIED')
            self.assertIsNone(report['scientific_certificate_dimensions']['uniform_gap_status'])

if __name__=='__main__':unittest.main()
