"""Nonlinear classwise objective: positive and adversarial exact rational checks."""
import copy
import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.engines.nonlinear import propose_nonlinear,FUNCTIONAL,POLICY_CLASS
from permansson_app.receipts.nonlinear import check_nonlinear
from permansson_app.errors import AppError


def model(actions=('stay',), world=('left','right')):
    states={'strategic':['s'],'world':list(world),'actions':list(actions)}
    feasible=[{'s':'s','x':x,'actions':list(actions)} for x in world]
    alpha=[{'s':'s','x':x,'weights':{a:('1' if a==actions[0] else '0') for a in actions}} for x in world]
    P=[];U=[]
    for x in world:
        for a in actions:
            dest=x if a=='stay' else ('right' if x=='left' else 'left')
            P.append({'s':'s','x':x,'a':a,'weights':{xp:('1' if xp==dest else '0') for xp in world}})
            for xp in world:U.append({'s':'s','x':x,'a':a,'xp':xp,'weights':{'s':'1'}})
    return {'format':'Permansson.App.FiniteStrategicWorld.v1','states':states,
            'feasible':feasible,'alpha':alpha,'P':P,'U':U}


def request(actions=('stay',),world=('left','right')):
    m=model(actions,world)
    return {'format':'Permansson.App.NonlinearStationaryRequest.v1','model':m,
            'descriptor_true_states':[['s',world[-1]]],
            'initial_law':[{'state':['s',x],'mass':('1/2' if len(world)==2 else ('1' if i==0 else '0'))}
                           for i,x in enumerate(world)],
            'functional_id':FUNCTIONAL,'policy_class':POLICY_CLASS}


class NonlinearStationaryTest(unittest.TestCase):
    def test_multichain_noncommuting_functional(self):
        req=request()
        r=propose_nonlinear(req)
        self.assertEqual(check_nonlinear(req,r)['status'],'PASS')
        self.assertEqual(r['policy_count'],1)
        p=r['policies'][0]
        self.assertEqual(p['expected_classwise_score'],'1/2')
        self.assertEqual(p['functional_of_expected_descriptor'],'5/6')
        self.assertEqual(p['occupation_receipt']['bottom_classes'],[[0],[1]])
        self.assertEqual(r['lean_status'],'NOT_EXECUTED')
        self.assertFalse(r['scientific_claims_verified'])

    def test_stationary_laws_beyond_the_input_precision_are_accepted(self):
        # Codex's case: every input rational is within the 256-bit input bound,
        # but the stationary probabilities need 398 bits.
        # left -> right with a = (2^199-1)/2^200, right -> left with b = (2^199-3)/(2^200-1).
        rows={'left':{'left':'%d/%d'%(2**199+1,2**200),'right':'%d/%d'%(2**199-1,2**200)},
              'right':{'left':'%d/%d'%(2**199-3,2**200-1),'right':'%d/%d'%(2**199+2,2**200-1)}}
        req=request()
        for row in req['model']['P']:row['weights']=rows[row['x']]
        r=propose_nonlinear(req)
        self.assertEqual(check_nonlinear(req,r)['status'],'PASS')
        law=r['policies'][0]['occupation_receipt']['stationary_laws'][0]
        bits=max(max(int(n).bit_length() for n in v.split('/')) for v in law)
        self.assertGreater(bits,256)

    def test_exhaustive_deterministic_policy_class(self):
        req=request(('stay','flip'))
        r=propose_nonlinear(req)
        self.assertEqual(r['policy_count'],4)
        self.assertEqual(check_nonlinear(req,r)['status'],'PASS')
        self.assertEqual(r['policies'][0]['selected_actions'],['stay','stay'])
        self.assertEqual(r['policies'][-1]['selected_actions'],['flip','flip'])
        self.assertEqual(r['optimum_value'],'5/6') # alternating two-state class has p=1/2
        self.assertEqual(r['attaining_policy_indices'],[3])

    def test_changed_class_value_fails(self):
        req=request();r=propose_nonlinear(req)
        r['policies'][0]['class_functional_values'][0]='1'
        with self.assertRaises(AppError):check_nonlinear(req,r)

    def test_illicit_barycenter_promotion_fails(self):
        req=request();r=propose_nonlinear(req)
        r['policies'][0]['expected_classwise_score']='5/6'
        with self.assertRaises(AppError):check_nonlinear(req,r)

    def test_omitted_policy_fails(self):
        req=request(('stay','flip'));r=propose_nonlinear(req)
        r['policies'].pop()
        with self.assertRaises(AppError):check_nonlinear(req,r)

    def test_false_optimum_fails(self):
        req=request(('stay','flip'));r=propose_nonlinear(req)
        r['optimum_value']='1'
        with self.assertRaises(AppError):check_nonlinear(req,r)

    def test_invalid_descriptor_duplicate(self):
        req=request();req['descriptor_true_states']*=2
        with self.assertRaises(AppError):propose_nonlinear(req)

    def test_wrong_initial_order(self):
        req=request();req['initial_law'].reverse()
        with self.assertRaises(AppError):propose_nonlinear(req)

    def test_unsupported_functional_is_error(self):
        req=request();req['functional_id']='arbitrary_user_code'
        with self.assertRaises(AppError):propose_nonlinear(req)

    def test_degenerate_no_hidden_seven_state_scope(self):
        req=request(world=('a','b','c','d','e','f','g','h','i'))
        with self.assertRaises(AppError):propose_nonlinear(req)

    def test_positive_probability_syntax_bound(self):
        req=request();req['initial_law'][0]['mass']=True
        with self.assertRaises(AppError):propose_nonlinear(req)

if __name__=='__main__':unittest.main()
