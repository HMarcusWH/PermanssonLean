"""Exact finite controlled invariant core: positive, negative and semantic mutants."""
from __future__ import annotations
import copy,json,os,subprocess,sys,tempfile,unittest
from fractions import Fraction
from pathlib import Path
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.safety import parse_safety_problem,propose_safety_core
from permansson_app.receipts.safety import check_safety_core
from permansson_app.schema_validate import validate_packaged_schema

class SafetyCoreTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.example=APP/'src/permansson_app/data/examples/finite_safety.v1.json'
        cls.input=json.loads(cls.example.read_text())
    def setUp(self):
        self.raw=copy.deepcopy(self.input)
        self.problem=parse_safety_problem(self.raw)
        self.receipt=propose_safety_core(self.problem)
    def check(self,raw=None,receipt=None):
        return check_safety_core(parse_safety_problem(raw or self.raw),receipt if receipt is not None else self.receipt)
    def mutation(self,key,value):
        bad=copy.deepcopy(self.receipt);bad[key]=value
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_core_and_exact_pruning(self):
        self.assertEqual(self.receipt['descending_pruning_chain'],[[0,1],[0],[0]])
        self.assertEqual(self.receipt['core_indices'],[0])
        self.assertEqual(self.receipt['stationary_witness_actions'],[{'state_index':0,'action':'stay'}])
        self.assertEqual(self.check()['status'],'PASS')
    def test_baseline_alpha_not_mistaken_for_optimized_policy(self):
        self.assertEqual(self.raw['model']['alpha'][0]['weights']['stay'],'0')
        self.assertEqual(self.receipt['stationary_witness_actions'][0]['action'],'stay')
    def test_outside_core_may_have_positive_infinite_survival_probability(self):
        # At x1, taking leak reaches the controlled invariant x0 with probability 1/2.
        # Therefore not-in-core does NOT imply zero probability of staying safe forever.
        self.assertEqual(Fraction(self.raw['model']['P'][3]['weights']['x0']),Fraction(1,2))
        self.assertIn('NO_ZERO_SURVIVAL_PROBABILITY',self.receipt['outside_core'])
    def test_all_states_safe_is_invariant(self):
        self.raw['safe'].append({'strategic':'s0','world':'x2'})
        p=parse_safety_problem(self.raw);r=propose_safety_core(p)
        self.assertEqual(r['descending_pruning_chain'],[[0,1,2],[0,1,2]])
        self.assertEqual(check_safety_core(p,r)['status'],'PASS')
    def test_empty_core_is_valid_and_not_false_zero(self):
        self.raw['safe']=[{'strategic':'s0','world':'x1'}]
        p=parse_safety_problem(self.raw);r=propose_safety_core(p)
        self.assertEqual(r['descending_pruning_chain'],[[1],[],[]])
        self.assertEqual(r['core_indices'],[])
        self.assertEqual(r['stationary_witness_actions'],[])
        self.assertEqual(check_safety_core(p,r)['status'],'PASS')
    def test_external_schema_valid(self):
        self.assertEqual(validate_packaged_schema('schemas/finite_safety.v1.schema.json',self.raw)['status'],'PASS')
    def test_empty_input_rejected(self):
        self.raw['safe']=[]
        with self.assertRaises(AppError):parse_safety_problem(self.raw)
    def test_duplicate_safe_rejected(self):
        self.raw['safe'].append(copy.deepcopy(self.raw['safe'][0]))
        with self.assertRaises(AppError):parse_safety_problem(self.raw)
    def test_foreign_state_rejected(self):
        self.raw['safe'][0]['world']='x9'
        with self.assertRaises(AppError):parse_safety_problem(self.raw)
    def test_extra_safe_key_rejected(self):
        self.raw['safe'][0]['surprise']=True
        with self.assertRaises(AppError):parse_safety_problem(self.raw)
    def test_numeric_state_label_rejected(self):
        self.raw['safe'][0]['world']=0
        with self.assertRaises(AppError):parse_safety_problem(self.raw)
    def test_forged_physical_transition_not_same_receipt(self):
        self.raw['model']['P'][0]['weights']={'x0':'3/4','x1':'0','x2':'1/4'}
        with self.assertRaises(AppError):self.check(raw=self.raw)
    def test_modified_feasible_choices_receipt_not_reusable(self):
        self.raw['model']['feasible'][0]['actions']=['leak']
        # Remove producer-inconsistent stay P/U rows, adjust alpha already leaky.
        self.raw['model']['P']=[r for r in self.raw['model']['P'] if not(r['x']=='x0' and r['a']=='stay')]
        self.raw['model']['U']=[r for r in self.raw['model']['U'] if not(r['x']=='x0' and r['a']=='stay')]
        with self.assertRaises(AppError):self.check(raw=self.raw)
    def test_wrong_semantic_identity(self):self.mutation('problem_semantic_identity',{'sha256':'0'*64})
    def test_wrong_model_identity(self):self.mutation('model_semantic_identity',{'sha256':'0'*64})
    def test_foreign_metadata(self):self.mutation('unexpected',True)
    def test_forged_initial_region(self):self.mutation('initial_safe_indices',[0])
    def test_wrong_joint_index_order(self):self.mutation('joint_states',list(reversed(self.receipt['joint_states'])))
    def test_missing_pruning_step(self):self.mutation('descending_pruning_chain',[[0,1],[0]])
    def test_forged_prune_one(self):self.mutation('descending_pruning_chain',[[0,1],[0,1],[0,1]])
    def test_forged_prune_without_proof(self):self.mutation('descending_pruning_chain',[[0,1],[],[]])
    def test_extra_stable_steps(self):self.mutation('descending_pruning_chain',[[0,1],[0],[0],[0]])
    def test_forged_core(self):self.mutation('core_indices',[0,1])
    def test_bad_policy_witness(self):self.mutation('stationary_witness_actions',[{'state_index':0,'action':'leak'}])
    def test_foreign_policy_witness(self):self.mutation('stationary_witness_actions',[{'state_index':1,'action':'stay'}])
    def test_missing_policy_witness(self):self.mutation('stationary_witness_actions',[])
    def test_duplicate_policy_witness(self):self.mutation('stationary_witness_actions',[{'state_index':0,'action':'stay'}]*2)
    def test_forged_lean_status(self):self.mutation('lean_status','PASS')
    def test_false_scientific_promotion(self):self.mutation('scientific_claims_verified',True)
    def test_baseline_promotion(self):self.mutation('baseline_alpha_policy_optimized_over',False)
    def test_false_zero_inference(self):self.mutation('outside_core','ZERO_SURVIVAL')
    def test_cli_produces_independently_checked_report(self):
        with tempfile.TemporaryDirectory() as d:
            out=Path(d)/'out'
            env=dict(os.environ,PYTHONPATH=str(APP/'src'),PYTHONDONTWRITEBYTECODE='1')
            r=subprocess.run([sys.executable,'-B','-m','permansson_app','finite-safety',str(self.example),'--output',str(out)],
                cwd=APP,env=env,capture_output=True,text=True,timeout=35)
            self.assertEqual(r.returncode,0,r.stdout+r.stderr)
            self.assertEqual(json.loads((out/'independent_check.json').read_text())['status'],'PASS')
            report=json.loads((out/'scientific_report.json').read_text())
            self.assertIsNone(report['scientific_certificate_dimensions']['validity'])
            self.assertEqual(report['empirical_identification'],'NOT_IDENTIFIED')
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(json.loads((out/'safety_core_receipt.json').read_text())['core_indices'],[0])

if __name__ == '__main__':unittest.main()
