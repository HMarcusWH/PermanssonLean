"""Exact recurrence, mutation and scientific-boundary tests for finite chains."""
from __future__ import annotations
import copy,json,os,subprocess,sys,tempfile,unittest
from fractions import Fraction
from pathlib import Path
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.errors import AppError
from permansson_app.finite_world import parse_finite_world,induced_kernel
from permansson_app.engines.occupation import compute_occupation,bottom_classes
from permansson_app.receipts.occupation import check_occupation
from permansson_app.engines.exit import parse_region,compute_exit
from permansson_app.receipts.exit import check_exit


def model_from_rows(rows):
    n=len(rows);states=[f'x{i}' for i in range(n)]
    def q(p):return str(p) if type(p) is str else str(Fraction(p))
    raw={'format':'Permansson.App.FiniteStrategicWorld.v1',
         'states':{'strategic':['s0'],'world':states,'actions':['a0']},
         'feasible':[{'s':'s0','x':x,'actions':['a0']} for x in states],
         'alpha':[{'s':'s0','x':x,'weights':{'a0':'1'}} for x in states],
         'P':[{'s':'s0','x':x,'a':'a0','weights':{y:q(v) for y,v in zip(states,row)}} for x,row in zip(states,rows)],
         'U':[{'s':'s0','x':x,'a':'a0','xp':xp,'weights':{'s0':'1'}} for x in states for xp in states]}
    return parse_finite_world(raw)


def region(model, indices, horizon):
    return parse_region({'format':'Permansson.App.FiniteRegion.v1','horizon':horizon,
        'joint_states':[{'strategic':'s0','world':model.world[i]} for i in indices]},model)


class OccupationTests(unittest.TestCase):
    def setUp(self):
        self.model=model_from_rows([['1','0','0'],['0','1','0'],['1/2','1/2','0']])
        self.receipt=compute_occupation(self.model)

    def test_absorbing_fork_random_vs_mean(self):
        r=self.receipt
        self.assertEqual(r['bottom_classes'],[[0],[1]])
        self.assertEqual(r['absorption_weights'][2],['1/2','1/2'])
        self.assertEqual(r['expected_limit_laws'][2],['1/2','1/2','0'])
        self.assertEqual(r['limit_interpretation'],'RANDOM_CLASS_STATIONARY_LAW_NOT_ITS_MEAN')
        self.assertEqual(check_occupation(self.model,r)['status'],'PASS')
    def test_periodic_occupation_not_pointwise_convergence(self):
        model=model_from_rows([['0','1'],['1','0']])
        r=compute_occupation(model)
        self.assertEqual(r['bottom_classes'],[[0,1]])
        self.assertEqual(r['stationary_laws'],[['1/2','1/2']])
        self.assertEqual(check_occupation(model,r)['status'],'PASS')
    def test_aperiodic_stationary(self):
        model=model_from_rows([['1/2','1/2'],['1/4','3/4']])
        r=compute_occupation(model)
        self.assertEqual(r['stationary_laws'],[['1/3','2/3']])
        self.assertEqual(check_occupation(model,r)['status'],'PASS')
    def test_completely_disconnected(self):
        model=model_from_rows([['1','0'],['0','1']])
        self.assertEqual(compute_occupation(model)['bottom_classes'],[[0],[1]])
    def test_unknown_zero_support_not_recurrent(self):
        model=model_from_rows([['0','1','0'],['0','0','1'],['0','0','1']])
        r=compute_occupation(model)
        self.assertEqual(r['bottom_classes'],[[2]])
        self.assertEqual(r['absorption_weights'],[['1'],['1'],['1']])
        self.assertEqual(check_occupation(model,r)['status'],'PASS')
    def test_false_stationary_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['stationary_laws'][0][0]='1/2'
        with self.assertRaises(AppError):check_occupation(self.model,bad)
    def test_absorption_mutation_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['absorption_weights'][2]=['3/4','1/4']
        with self.assertRaises(AppError):check_occupation(self.model,bad)
    def test_mean_mutation_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['expected_limit_laws'][2]=['1','0','0']
        with self.assertRaises(AppError):check_occupation(self.model,bad)
    def test_omitted_class_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['bottom_classes']=[[0]]
        with self.assertRaises(AppError):check_occupation(self.model,bad)
    def test_wrong_scientific_status_rejected(self):
        for field,val in [('scientific_claims_verified',True),('lean_status','PASSED'),('limit_interpretation','DETERMINISTIC_MEAN')]:
            with self.subTest(field=field):
                bad=copy.deepcopy(self.receipt);bad[field]=val
                with self.assertRaises(AppError):check_occupation(self.model,bad)
    def test_canonical_input_bound(self):
        bad=copy.deepcopy(self.receipt);bad['model_semantic_identity']['sha256']='0'*64
        with self.assertRaises(AppError):check_occupation(self.model,bad)


class ExitTests(unittest.TestCase):
    def setUp(self):
        self.model=model_from_rows([['1/2','1/2'],['0','1']])
        self.region=region(self.model,[0],4)
        self.receipt=compute_exit(self.model,self.region)
    def test_geometric_first_exit_and_tail(self):
        row=self.receipt['rows'][0]
        self.assertEqual(row['survival_through'],['1','1/2','1/4','1/8','1/16'])
        self.assertEqual(row['eventual_exit_by_destination'],['1'])
        self.assertEqual(row['never_exit'],'0')
        self.assertEqual(row['first_exit_by_step_and_destination'],[['1/2'],['1/4'],['1/8'],['1/16']])
        self.assertEqual(check_exit(self.model,self.region,self.receipt)['status'],'PASS')
    def test_results_beyond_the_input_precision_are_checked(self):
        # 1/1024 survival over 26 steps is 1/2**260: a correct result larger than
        # any admissible input rational. The checker parses results with the
        # result-sized bound, so the engine's receipt passes and a forgery fails.
        model=model_from_rows([['1/1024','1023/1024'],['0','1']])
        deep=region(model,[0],26)
        receipt=compute_exit(model,deep)
        self.assertEqual(receipt['rows'][0]['survival_through'][-1],'1/'+str(2**260))
        self.assertEqual(check_exit(model,deep,receipt)['status'],'PASS')
        forged=copy.deepcopy(receipt)
        forged['rows'][0]['survival_through'][-1]='1/'+str(2**260+1)
        with self.assertRaises(AppError):
            check_exit(model,deep,forged)
    def test_horizon_zero(self):
        r=region(self.model,[0],0);x=compute_exit(self.model,r)
        self.assertEqual(x['rows'][0]['survival_through'],['1'])
        self.assertEqual(x['rows'][0]['first_exit_by_step_and_destination'],[])
        self.assertEqual(check_exit(self.model,r,x)['status'],'PASS')
    def test_never_exit_closed_class(self):
        model=model_from_rows([['1','0'],['0','1']]);r=region(model,[0],3)
        receipt=compute_exit(model,r)
        self.assertEqual(receipt['rows'][0]['never_exit'],'1')
        self.assertEqual(receipt['rows'][0]['eventual_exit_by_destination'],['0'])
        self.assertEqual(check_exit(model,r,receipt)['status'],'PASS')
    def test_partial_eventual_never_exit_mass(self):
        model=model_from_rows([['0','1/2','1/2'],['0','1','0'],['0','0','1']]);r=region(model,[0,1],3)
        receipt=compute_exit(model,r)
        self.assertEqual(receipt['rows'][0]['eventual_exit_by_destination'],['1/2'])
        self.assertEqual(receipt['rows'][0]['never_exit'],'1/2')
        self.assertEqual(receipt['rows'][1]['never_exit'],'1')
        self.assertEqual(receipt['rows'][0]['survival_through'],['1','1/2','1/2','1/2'])
        self.assertEqual(check_exit(model,r,receipt)['status'],'PASS')
    def test_full_region_no_exit(self):
        r=region(self.model,[0,1],3);v=compute_exit(self.model,r)
        self.assertEqual(v['rows'][0]['eventual_exit_by_destination'],[])
        self.assertEqual(v['rows'][0]['never_exit'],'1')
        self.assertEqual(check_exit(self.model,r,v)['status'],'PASS')
    def test_region_subset_is_semantic(self):
        full=region(self.model,[0,1],4)
        self.assertNotEqual(full.semantic_id,self.region.semantic_id)
    def test_false_survival_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['rows'][0]['survival_through'][3]='1/7'
        with self.assertRaises(AppError):check_exit(self.model,self.region,bad)
    def test_false_destination_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['rows'][0]['first_exit_by_step_and_destination'][0][0]='0'
        with self.assertRaises(AppError):check_exit(self.model,self.region,bad)
    def test_false_eventual_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['rows'][0]['eventual_exit_by_destination']=['1/2'];bad['rows'][0]['never_exit']='1/2'
        with self.assertRaises(AppError):check_exit(self.model,self.region,bad)
    def test_forged_science_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['scientific_claims_verified']=True
        with self.assertRaises(AppError):check_exit(self.model,self.region,bad)
    def test_region_negative_inputs(self):
        valid={'format':'Permansson.App.FiniteRegion.v1','joint_states':[{'strategic':'s0','world':'x0'}],'horizon':4}
        for key,value in [('horizon',True),('horizon',65),('joint_states',[]),('joint_states',[{'strategic':'s0','world':'x7'}]),('joint_states',[{'strategic':'s0','world':'x0'},{'strategic':'s0','world':'x0'}])]:
            with self.subTest(key=key,value=value):
                bad={**valid,key:value}
                with self.assertRaises(AppError):parse_region(bad,self.model)
    def test_wrong_region_identity_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['region_semantic_identity']['sha256']='a'*64
        with self.assertRaises(AppError):check_exit(self.model,self.region,bad)
    def test_horizon_mismatch_rejected(self):
        bad=copy.deepcopy(self.receipt);bad['horizon']=3
        with self.assertRaises(AppError):check_exit(self.model,self.region,bad)


class InstalledCLIContracts(unittest.TestCase):
    def test_occupation_and_exit_cli(self):
        root=APP/'src/permansson_app/data/examples'
        env={**os.environ,'PYTHONPATH':str(APP/'src'),'PYTHONDONTWRITEBYTECODE':'1'}
        with tempfile.TemporaryDirectory() as tmp:
            for cmd,n in [('finite-occupation','occupation_receipt.json'),('finite-exit','exit_receipt.json')]:
                args=[sys.executable,'-B','-m','permansson_app',cmd,str(root/'finite_world.v1.model.json')]
                if cmd=='finite-exit':args.append(str(root/'finite_region.v1.json'))
                args+=['--output',str(Path(tmp)/cmd)]
                result=subprocess.run(args,cwd=APP,env=env,capture_output=True,text=True,timeout=20)
                self.assertEqual(result.returncode,0,result.stderr)
                r=json.loads((Path(tmp)/cmd/n).read_text())
                self.assertEqual(r['lean_status'],'NOT_EXECUTED')
                report=json.loads((Path(tmp)/cmd/'scientific_report.json').read_text())
                self.assertFalse(report['scientific_claims_verified'])
                self.assertEqual(report['independent_mathematical_certification'],'NOT_ASSESSED')

if __name__=='__main__':unittest.main()
