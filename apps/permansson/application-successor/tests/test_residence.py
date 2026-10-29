"""Residence monitor literal timing, adversaries, and Bellman certificate checks."""
import copy
import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.engines.monitors import parse_residence
from permansson_app.engines.residence import solve_residence
from permansson_app.receipts.residence import check_residence
from permansson_app.errors import AppError


def model(world, next_state):
    return {'format':'Permansson.App.FiniteStrategicWorld.v1',
        'states':{'strategic':['s'],'world':world,'actions':['go']},
        'feasible':[{'s':'s','x':x,'actions':['go']} for x in world],
        'alpha':[{'s':'s','x':x,'weights':{'go':'1'}} for x in world],
        'P':[{'s':'s','x':x,'a':'go','weights':{y:('1' if y==next_state[x] else '0') for y in world}} for x in world],
        'U':[{'s':'s','x':x,'a':'go','xp':y,'weights':{'s':'1'}} for x in world for y in world]}


def request(world=('A','B','C','D'), transitions=None, target=('B','D'), danger=(), mode='retryable',deadline=3,dwell=1,time_type='entry_by',start='A'):
    if transitions is None:transitions={'A':'B','B':'C','C':'D','D':'D'}
    return {'format':'Permansson.App.FiniteResidenceRequest.v1','model':model(list(world),transitions),
        'target':[{'strategic':'s','world':x} for x in target],
        'danger':[{'strategic':'s','world':x} for x in danger],
        'mode':mode,'deadline':deadline,'deadline_semantics':time_type,
        'dwell_transitions':dwell,
        'initial_law':[{'state':['s',x],'mass':('1' if x==start else '0')} for x in world]}


class MonitorSemantics(unittest.TestCase):
    def test_retryable_differs_from_first_ever(self):
        retry=request(mode='retryable')
        first=request(mode='first_entry')
        a=solve_residence(retry);b=solve_residence(first)
        self.assertEqual(a['optimal_success_probability'],'1')
        self.assertEqual(b['optimal_success_probability'],'0')
        self.assertEqual(check_residence(retry,a)['status'],'PASS')
        self.assertEqual(check_residence(first,b)['status'],'PASS')
        self.assertEqual(a['horizon'],4)
    def test_time_zero_goal_requires_m_plus_one_observations(self):
        raw=request(world=('A','B'),transitions={'A':'A','B':'B'},target=('B',),start='B',deadline=0,dwell=0)
        res=solve_residence(raw)
        self.assertEqual(res['optimal_success_probability'],'1')
        self.assertEqual(res['initial_monitor_states'],['failed','success'])
        self.assertEqual(check_residence(raw,res)['status'],'PASS')
    def test_entry_by_and_completion_by_differ(self):
        kwargs={'world':('A','B'),'transitions':{'A':'B','B':'B'},'target':('B',),'deadline':1,'dwell':1}
        a=request(time_type='entry_by',**kwargs)
        b=request(time_type='completion_by',**kwargs)
        self.assertEqual(solve_residence(a)['optimal_success_probability'],'1')
        self.assertEqual(solve_residence(b)['optimal_success_probability'],'0')
    def test_two_action_bellman_chooses_realized_control(self):
        from test_nonlinear import model as two_action_world
        raw=request(world=('left','right'),transitions={'left':'left','right':'right'},
                    target=('right',),start='left',deadline=1,dwell=0)
        raw['model']=two_action_world(('stay','flip'),('left','right'))
        output=solve_residence(raw)
        self.assertEqual(output['optimal_success_probability'],'1')
        # The last monitor column is successful, while search at t=0
        # must select flip to reach the target before the deadline.
        self.assertEqual(output['chosen_actions_by_observation_time'][0][0][0],'flip')
        self.assertEqual(check_residence(raw,output)['status'],'PASS')
        output['chosen_actions_by_observation_time'][0][0][0]='stay'
        with self.assertRaises(AppError):check_residence(raw,output)
    def test_two_action_tied_optimum_is_complete(self):
        from test_nonlinear import model as two_action_world
        raw=request(world=('left','right'),transitions={'left':'left','right':'right'},
                    target=('right',),start='right',deadline=0,dwell=0)
        raw['model']=two_action_world(('stay','flip'),('left','right'))
        output=solve_residence(raw)
        self.assertEqual(check_residence(raw,output)['status'],'PASS')
        self.assertEqual(output['optimal_success_probability'],'1')
    def test_avoid_danger_precedes_simultaneous_success(self):
        raw=request(mode='avoid',danger=('D',),deadline=4,dwell=1,time_type='completion_by')
        out=solve_residence(raw)
        self.assertEqual(out['optimal_success_probability'],'0')
        self.assertEqual(check_residence(raw,out)['status'],'PASS')
    def test_danger_after_success_does_not_retroactively_fail(self):
        raw=request(world=('A','B','C'),transitions={'A':'B','B':'B','C':'C'},
                    target=('B',),danger=('C',),mode='avoid',deadline=3,dwell=1,time_type='completion_by')
        p=parse_residence(raw)
        self.assertEqual(p.observe('success',2,3),'success')
        self.assertEqual(solve_residence(raw)['optimal_success_probability'],'1')
    def test_impossible_completion_horizon_fails(self):
        raw=request(mode='first_entry',deadline=0,dwell=1,time_type='completion_by')
        with self.assertRaises(AppError):solve_residence(raw)
    def test_bool_deadline_rejected(self):
        raw=request();raw['deadline']=True
        with self.assertRaises(AppError):solve_residence(raw)
    def test_unknown_source_action_rejected(self):
        raw=request();raw['model']['feasible'][0]['actions']=['fake']
        with self.assertRaises(AppError):solve_residence(raw)
    def test_wrong_monitor_value_rejected(self):
        raw=request();res=solve_residence(raw)
        res['values_by_observation_time'][0][0][0]='0'
        with self.assertRaises(AppError):check_residence(raw,res)
    def test_wrong_optimizer_rejected(self):
        raw=request();res=solve_residence(raw)
        res['chosen_actions_by_observation_time'][0][0][0]='fake'
        with self.assertRaises(AppError):check_residence(raw,res)
    def test_unknown_claim_is_rejected(self):
        raw=request();res=solve_residence(raw)
        res['lean_status']='CERTIFIED'
        with self.assertRaises(AppError):check_residence(raw,res)
    def test_removed_time_row_fails(self):
        raw=request();res=solve_residence(raw)
        res['values_by_observation_time'].pop()
        with self.assertRaises(AppError):check_residence(raw,res)
    def test_full_probability_boundary(self):
        raw=request(world=('A','B'),transitions={'A':'B','B':'B'},target=('B',),start='A',deadline=2,dwell=1)
        raw['initial_law'][0]['mass']='1/2';raw['initial_law'][1]['mass']='1/2'
        out=solve_residence(raw)
        self.assertEqual(out['optimal_success_probability'],'1')
        self.assertEqual(check_residence(raw,out)['status'],'PASS')

if __name__=='__main__':unittest.main()
