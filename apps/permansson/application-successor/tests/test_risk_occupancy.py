"""Original-kernel binding, randomized optimum, and risk LP adversaries."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.risk_occupancy import propose_risk,parse_risk,reconstruct_policy
from permansson_app.receipts.risk_occupancy import check_risk
from permansson_app.finite_world import exact_ratio
from permansson_app.identity import rational_text

FIXTURE=Path(__file__).resolve().parents[1]/'src/permansson_app/data/examples/risk_occupancy.v1.json'
def request():return json.loads(FIXTURE.read_text())

def high_precision(req,cap=None):
    """Codex's case: every transition's danger probability is 1/2^200 and the
    danger reward 1/3^100. Each input is within the 256-bit input bound; the
    generated objective coefficient has a 359-bit denominator."""
    p=Fraction(1,2**200)
    for row in req['model']['P']:
        row['weights']={'danger':rational_text(p),'safe':rational_text(1-p)}
    for row in req['terminal_rewards']:
        row['value']='0' if row['state'][1]=='safe' else rational_text(Fraction(1,3**100))
    if cap is not None:req['risk_cap']=cap
    return req

class RiskOccupancyTests(unittest.TestCase):
    def test_generated_lp_coefficients_beyond_the_input_precision(self):
        req=high_precision(request())
        q=parse_risk(req)
        self.assertGreater(max(c.denominator.bit_length() for c in q.lp.coeffs),256)
        r=propose_risk(req)
        self.assertEqual(check_risk(req,r)['status'],'PASS')
        # An external LP request is still held to the input bound.
        from permansson_app.engines.lp_types import parse_lp
        with self.assertRaises(AppError) as raised:parse_lp(q.lp.normalized_payload())
        self.assertIn(raised.exception.code,{'RATIONAL_SIZE','RATIONAL_FORMAT'})
        self.assertEqual(parse_lp(q.lp.normalized_payload(),generated=True).coeffs,q.lp.coeffs)

    def test_true_fractional_optimum_not_deterministic_policy(self):
        req=request();r=propose_risk(req)
        self.assertEqual(check_risk(req,r)['status'],'PASS')
        self.assertEqual(r['lp_certificate']['primal'],['1/2','1/2','0','0'])
        self.assertEqual(r['expected_terminal_reward'],'1/2')
        self.assertEqual(r['next_step_risk_probability'],'1/2')
        self.assertEqual(r['next_state_law'],['1/2','1/2'])
        self.assertEqual(r['policy'][0]['action_weights'],{'stay':'1/2','gamble':'1/2'})
        self.assertEqual(r['policy'][1]['action_weights'],{'stay':'1','gamble':'0'})
        self.assertTrue(r['policy'][1]['zero_mass_default_used'])
        self.assertEqual(r['optimization_scope'],'one_transition_fully_observed_randomized_Markov_from_declared_initial_law')
        self.assertFalse(r['scientific_claims_verified'])
        self.assertEqual(r['lean_status'],'NOT_EXECUTED')

    def test_zero_risk_cap_forces_safe_action(self):
        req=request();req['risk_cap']='0'
        r=propose_risk(req)
        self.assertEqual(check_risk(req,r)['status'],'PASS')
        self.assertEqual(r['expected_terminal_reward'],'0')
        self.assertEqual(r['policy'][0]['action_weights'],{'stay':'1','gamble':'0'})

    def test_full_risk_budget_allows_risky_action(self):
        req=request();req['risk_cap']='1'
        r=propose_risk(req)
        self.assertEqual(check_risk(req,r)['status'],'PASS')
        self.assertEqual(r['expected_terminal_reward'],'1')
        self.assertEqual(r['next_step_risk_probability'],'1')

    def test_arbitrary_tied_optimum_not_equal_reference_primal(self):
        req=request();req['risk_cap']='1'
        for row in req['terminal_rewards']:row['value']='0'
        r=propose_risk(req);self.assertEqual(check_risk(req,r)['status'],'PASS')
        primal=tuple(exact_ratio(x) for x in r['lp_certificate']['primal'])
        other=(Fraction(0),Fraction(1),Fraction(0),Fraction(0)) if primal[0]==1 else (Fraction(1),Fraction(0),Fraction(0),Fraction(0))
        p=parse_risk(req)
        policy,law=reconstruct_policy(p,other)
        r['lp_certificate']['primal']=[rational_text(x) for x in other]
        r['policy']=policy
        r['next_state_law']=[rational_text(x) for x in law]
        r['next_step_risk_probability']=rational_text(law[1])
        self.assertEqual(check_risk(req,r)['status'],'PASS')

    def test_two_positive_initial_states(self):
        req=request();req['initial_law']=[{'state':['s','safe'],'mass':'1/2'},
                                           {'state':['s','danger'],'mass':'1/2'}]
        req['risk_cap']='3/4'
        r=propose_risk(req)
        self.assertEqual(check_risk(req,r)['status'],'PASS')
        self.assertEqual(r['next_step_risk_probability'],'3/4')
        self.assertEqual(r['expected_terminal_reward'],'3/4')
        self.assertFalse(r['policy'][1]['zero_mass_default_used'])

    def test_infeasible_search_is_not_a_false_farkas_certificate(self):
        req=request();req['risk_cap']='0'
        for row in req['model']['P']:
            if row['x']=='safe':row['weights']={'safe':'0','danger':'1'}
        with self.assertRaises(AppError) as err:propose_risk(req)
        self.assertEqual(err.exception.code,'RISK_NO_CERTIFICATE')
        self.assertIn('neither optimum nor infeasibility proved',str(err.exception))

    def test_duplicate_and_missing_input_support(self):
        r=request();r['initial_law'][1]=deepcopy(r['initial_law'][0])
        with self.assertRaises(AppError):parse_risk(r)
        r=request();r['terminal_rewards'].pop()
        with self.assertRaises(AppError):parse_risk(r)
        r=request();r['risk_states']=[['s','alien']]
        with self.assertRaises(AppError):parse_risk(r)

    def test_float_boolean_and_negative_input_rejected(self):
        r=request();r['risk_cap']=True
        with self.assertRaises(AppError):parse_risk(r)
        r=request();r['initial_law'][0]['mass']='-1/2'
        with self.assertRaises(AppError):parse_risk(r)
        r=request();r['terminal_rewards'][1]['value']=.5
        with self.assertRaises(AppError):parse_risk(r)

    def test_risk_cap_source_identity_bound(self):
        req=request();r=propose_risk(req)
        req['risk_cap']='3/4'
        with self.assertRaises(AppError):check_risk(req,r)

    def test_mutated_original_P_cannot_reuse_receipt(self):
        req=request();r=propose_risk(req)
        q=deepcopy(req)
        for row in q['model']['P']:
            if row['x']=='safe' and row['a']=='stay':row['weights']={'safe':'0','danger':'1'}
        with self.assertRaises(AppError):check_risk(q,r)

    def test_all_critical_receipt_tamper_rejected(self):
        req=request();original=propose_risk(req)
        bads=[
            ('expected_terminal_reward',lambda r:r.__setitem__('expected_terminal_reward','1')),
            ('risk_probability',lambda r:r.__setitem__('next_step_risk_probability','0')),
            ('next_law',lambda r:r['next_state_law'].__setitem__(0,'1')),
            ('primal',lambda r:r['lp_certificate']['primal'].__setitem__(0,'1')),
            ('dual',lambda r:r['lp_certificate']['dual'].__setitem__(0,'-1')),
            ('lp_identity',lambda r:r['lp_model_identity'].__setitem__('sha256','0'*64)),
            ('physical_kernel',lambda r:r['controlled_next_rows'][1].__setitem__(1,'0')),
            ('reward_coeff',lambda r:r['objective_coefficients'].__setitem__(1,'0')),
            ('risk_coeff',lambda r:r['risk_coefficients'].__setitem__(1,'0')),
            ('zero_default',lambda r:r['policy'][1]['action_weights'].__setitem__('gamble','1')),
            ('source_binding',lambda r:r['source_model_identity'].__setitem__('sha256','0'*64)),
            ('false_lean',lambda r:r.__setitem__('lean_status','PASSED')),
            ('false_science',lambda r:r.__setitem__('scientific_claims_verified',True)),
            ('false_bool',lambda r:r['policy'][1].__setitem__('zero_mass_default_used',1)),
        ]
        for label,mutate in bads:
            with self.subTest(label=label):
                x=deepcopy(original);mutate(x)
                with self.assertRaises(AppError):check_risk(req,x)

    def test_unsupported_occupied_flow_dimensions(self):
        req=request();req['model']['states']['actions'].append('extra')
        for row in req['model']['feasible']:row['actions'].append('extra')
        for row in req['model']['alpha']:row['weights']['extra']='0'
        for state in req['model']['states']['world']:
            req['model']['P'].append({'s':'s','x':state,'a':'extra','weights':{'safe':'1','danger':'0'}})
            for xp in req['model']['states']['world']:
                req['model']['U'].append({'s':'s','x':state,'a':'extra','xp':xp,'weights':{'s':'1'}})
        with self.assertRaises(AppError) as e:parse_risk(req)
        self.assertEqual(e.exception.code,'RISK_SCOPE')

    def test_wrong_receipt_fields_and_invented_approval_rejected(self):
        req=request();r=propose_risk(req);r.pop('risk_indices')
        with self.assertRaises(AppError):check_risk(req,r)
        r=propose_risk(req);r['publication_approved']=True
        with self.assertRaises(AppError):check_risk(req,r)

if __name__=='__main__':unittest.main()
