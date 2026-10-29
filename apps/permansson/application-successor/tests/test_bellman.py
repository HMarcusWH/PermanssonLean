"""D1-B numeric Bellman table, attainable-policy and semantic mutation tests."""
from __future__ import annotations
import copy,json,os,subprocess,sys,tempfile,unittest
from pathlib import Path
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.hitting import parse_hitting_problem,propose_bellman
from permansson_app.receipts.control import check_bellman
from permansson_app.schema_validate import validate_packaged_schema
EXAMPLE=APP/'src/permansson_app/data/examples/control_hitting.v1.json'

class BellmanTests(unittest.TestCase):
    def setUp(self):
        self.data=json.loads(EXAMPLE.read_text())
        self.problem=parse_hitting_problem(self.data)
        self.receipt=propose_bellman(self.problem)
    def check(self,raw=None,receipt=None):
        return check_bellman(raw or self.problem,receipt or self.receipt)
    def test_original_exact_recurrence(self):
        r=self.receipt
        self.assertEqual(r['values_by_remaining_transitions'],[['0','1'],['1','1'],['1','1'],['1','1']])
        self.assertEqual(r['selected_actions_by_remaining_transitions'][1],['move',None])
        self.assertEqual(r['argmax_actions_by_remaining_transitions'][2][0],['stay','move'])
        self.assertEqual(self.check()['status'],'PASS')
    def test_baseline_alpha_not_optimized_result(self):
        self.assertEqual(self.data['model']['alpha'][0]['weights'],{'stay':'1','move':'0'})
        self.assertEqual(self.receipt['selected_actions_by_remaining_transitions'][1][0],'move')
        self.assertTrue(self.receipt['baseline_alpha_optimized_over_not_assumed_equilibrium'])
        self.assertFalse(self.receipt['scientific_claims_verified'])
    def test_tied_optimum_different_controller_is_valid(self):
        r=copy.deepcopy(self.receipt)
        r['selected_actions_by_remaining_transitions'][2][0]='move'
        self.assertEqual(self.check(receipt=r)['status'],'PASS')
    def test_goal_terminal_but_P_not_absorbing(self):
        raw=copy.deepcopy(self.data)
        # Physical dynamics can leave x1, but a reached goal is terminal for
        # hitting evaluation; no fictional mutation of P/U occurs.
        for row in raw['model']['P']:
            if row['x']=='x1':row['weights']={'x0':'1','x1':'0'}
        problem=parse_hitting_problem(raw);receipt=propose_bellman(problem)
        self.assertEqual([row[1] for row in receipt['values_by_remaining_transitions']],['1']*4)
        self.assertEqual(check_bellman(problem,receipt)['status'],'PASS')
    def test_forbidden_terminal_even_if_action_escapes(self):
        raw=copy.deepcopy(self.data);raw['forbidden']=[{'strategic':'s0','world':'x0'}]
        problem=parse_hitting_problem(raw);receipt=propose_bellman(problem)
        self.assertTrue(all(row[0]=='0' for row in receipt['values_by_remaining_transitions']))
        self.assertEqual(check_bellman(problem,receipt)['status'],'PASS')
    def test_horizon_zero(self):
        raw=copy.deepcopy(self.data);raw['horizon']=0
        p=parse_hitting_problem(raw);r=propose_bellman(p)
        self.assertEqual(len(r['values_by_remaining_transitions']),1)
        self.assertEqual(r['selected_actions_by_remaining_transitions'][0],[None,None])
        self.assertEqual(check_bellman(p,r)['status'],'PASS')
    def test_no_goal(self):
        raw=copy.deepcopy(self.data);raw['goal']=[]
        p=parse_hitting_problem(raw);r=propose_bellman(p)
        self.assertEqual(r['values_by_remaining_transitions'],[['0','0']]*4)
        self.assertEqual(check_bellman(p,r)['status'],'PASS')
    def test_admissibility_changes_attainable_value(self):
        raw=copy.deepcopy(self.data)
        raw['model']['feasible'][0]['actions']=['stay']
        raw['model']['P']=[row for row in raw['model']['P'] if not (row['x']=='x0' and row['a']=='move')]
        raw['model']['U']=[row for row in raw['model']['U'] if not (row['x']=='x0' and row['a']=='move')]
        p=parse_hitting_problem(raw);r=propose_bellman(p)
        self.assertEqual([row[0] for row in r['values_by_remaining_transitions']],['0']*4)
        self.assertEqual(check_bellman(p,r)['status'],'PASS')
    def test_full_schema_without_external_fetch(self):
        self.assertEqual(validate_packaged_schema('schemas/control_hitting.v1.schema.json',self.data)['status'],'PASS')
    def test_boolean_horizon_rejected(self):
        bad=copy.deepcopy(self.data);bad['horizon']=True
        with self.assertRaises(AppError):parse_hitting_problem(bad)
    def test_too_many_steps_rejected(self):
        bad=copy.deepcopy(self.data);bad['horizon']=25
        with self.assertRaises(AppError):parse_hitting_problem(bad)
    def test_overlap_goal_forbidden_rejected(self):
        bad=copy.deepcopy(self.data);bad['forbidden']=copy.deepcopy(bad['goal'])
        with self.assertRaises(AppError):parse_hitting_problem(bad)
    def test_duplicate_goal_rejected(self):
        bad=copy.deepcopy(self.data);bad['goal']+=copy.deepcopy(bad['goal'])
        with self.assertRaises(AppError):parse_hitting_problem(bad)
    def test_unknown_state_rejected(self):
        bad=copy.deepcopy(self.data);bad['goal']=[{'strategic':'s0','world':'x9'}]
        with self.assertRaises(AppError):parse_hitting_problem(bad)
    def test_forged_value_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['values_by_remaining_transitions'][1][0]='1/2'
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_nonattaining_choice_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['selected_actions_by_remaining_transitions'][1][0]='stay'
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_forged_argmax_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['argmax_actions_by_remaining_transitions'][2][0]=['stay']
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_missing_policy_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['selected_actions_by_remaining_transitions'][1]=[None,None]
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_wrong_goal_terminal_entry_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['values_by_remaining_transitions'][3][1]='0'
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_altered_target_identity_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['problem_semantic_identity']['sha256']='0'*64
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_claim_promotion_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['lean_status']='COMPILER_PASSED'
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_missing_table_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['values_by_remaining_transitions'].pop()
        with self.assertRaises(AppError):self.check(receipt=bad)
    def test_wrong_time_direction_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['values_by_remaining_transitions'].reverse()
        with self.assertRaises(AppError):self.check(receipt=bad)

class BellmanCLITests(unittest.TestCase):
    def test_installed_style_bellman(self):
        with tempfile.TemporaryDirectory() as temp:
            out=Path(temp)/'bellman'
            env={**os.environ,'PYTHONPATH':str(APP/'src'),'PYTHONDONTWRITEBYTECODE':'1'}
            p=subprocess.run([sys.executable,'-B','-m','permansson_app','finite-bellman',str(EXAMPLE),'--output',str(out)],
                             cwd=APP,env=env,text=True,capture_output=True,timeout=30)
            self.assertEqual(p.returncode,0,p.stderr)
            checker=json.loads((out/'independent_check.json').read_text())
            report=json.loads((out/'scientific_report.json').read_text())
            self.assertEqual(checker['status'],'PASS')
            self.assertFalse(report['scientific_claims_verified'])
            self.assertEqual(report['kernel_checked_proof'],'NOT_EXECUTED')
    def test_invalid_schema_failed_before_output(self):
        bad={'format':'Permansson.App.FiniteHittingControl.v1','model':{'format':'unknown'},'goal':[],'forbidden':[],'horizon':1}
        with tempfile.TemporaryDirectory() as temp:
            root=Path(temp);(root/'bad.json').write_text(json.dumps(bad))
            env={**os.environ,'PYTHONPATH':str(APP/'src'),'PYTHONDONTWRITEBYTECODE':'1'}
            p=subprocess.run([sys.executable,'-B','-m','permansson_app','finite-bellman',str(root/'bad.json'),'--output',str(root/'out')],
                             cwd=APP,env=env,text=True,capture_output=True,timeout=30)
            self.assertEqual(p.returncode,2)
            self.assertFalse((root/'out').exists())

if __name__=='__main__':unittest.main()
