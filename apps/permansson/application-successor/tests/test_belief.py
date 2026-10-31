"""One-step Bayesian observation-control positive, negative and semantic fixtures."""
from __future__ import annotations
from copy import deepcopy
from pathlib import Path
import json
import sys
import unittest
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.engines.belief import propose_belief,parse_belief
from permansson_app.receipts.belief import check_belief
from permansson_app.errors import AppError

FIXTURE=APP/'src/permansson_app/data/examples/belief.v1.json'
def req():return json.loads(FIXTURE.read_text())

class OneStepBelief(unittest.TestCase):
    def test_posterior_unreachable_and_observation_benefit(self):
        q=req();r=propose_belief(q);c=check_belief(q,r)
        self.assertEqual(c['status'],'PASS')
        self.assertEqual(c['bounded_policies_exhaustively_checked'],4)
        self.assertEqual(r['policy'][0]['posterior'],['3/4','1/4'])
        self.assertEqual(r['policy'][0]['selected_action'],'leave')
        self.assertEqual(r['policy'][1]['selected_action'],'repair')
        self.assertEqual(r['policy'][1]['posterior'],['1/4','3/4'])
        self.assertEqual(r['policy'][2]['observation_probability'],'0')
        self.assertIsNone(r['policy'][2]['posterior'])
        self.assertIsNone(r['policy'][2]['selected_action'])
        self.assertEqual(r['optimal_expected_terminal_reward'],'13/16')
        self.assertEqual(r['best_blind_policy_reward'],'3/4')
        self.assertEqual(r['value_of_observation'],'1/16')
        self.assertEqual(r['next_world_law'],['13/16','3/16'])
        self.assertFalse(r['scientific_claims_verified'])
        self.assertEqual(r['lean_status'],'NOT_EXECUTED')

    def test_perfect_signal_allows_different_legal_action_for_each_hidden_support(self):
        q=req()
        q['likelihoods']=[{'x':'healthy','weights':{'green':'1','red':'0','unseen':'0'}},
                          {'x':'damaged','weights':{'green':'0','red':'1','unseen':'0'}}]
        q['model']['feasible']=[{'s':'s','x':'healthy','actions':['leave']},
                                {'s':'s','x':'damaged','actions':['repair']}]
        q['model']['alpha'][1]['weights']={'leave':'0','repair':'1'}
        q['model']['P']=[r for r in q['model']['P'] if (r['x']=='healthy' and r['a']=='leave') or (r['x']=='damaged' and r['a']=='repair')]
        q['model']['U']=[r for r in q['model']['U'] if (r['x']=='healthy' and r['a']=='leave') or (r['x']=='damaged' and r['a']=='repair')]
        r=propose_belief(q)
        self.assertEqual(check_belief(q,r)['status'],'PASS')
        self.assertIsNone(r['best_blind_policy_reward'])
        self.assertIsNone(r['value_of_observation'])
        self.assertEqual(r['optimal_expected_terminal_reward'],'1')
        self.assertEqual([x['selected_action'] for x in r['policy']],['leave','repair',None])

    def test_shared_action_menu_cannot_exploit_hidden_state(self):
        q=req()
        q['model']['feasible']=[{'s':'s','x':'healthy','actions':['leave']},
                                {'s':'s','x':'damaged','actions':['repair']}]
        q['model']['alpha'][1]['weights']={'leave':'0','repair':'1'}
        q['model']['P']=[r for r in q['model']['P'] if (r['x']=='healthy' and r['a']=='leave') or (r['x']=='damaged' and r['a']=='repair')]
        q['model']['U']=[r for r in q['model']['U'] if (r['x']=='healthy' and r['a']=='leave') or (r['x']=='damaged' and r['a']=='repair')]
        with self.assertRaises(AppError) as e:propose_belief(q)
        self.assertEqual(e.exception.code,'BELIEF_COMMON_MENU')

    def test_invalid_observation_likelihood_row_sum(self):
        q=req();q['likelihoods'][1]['weights']['red']='1/2'
        with self.assertRaises(AppError):propose_belief(q)

    def test_missing_and_duplicate_observation_and_prior_support(self):
        for mutate in (
            lambda q:q['observations'].append('green'),
            lambda q:q['prior'].pop(),
            lambda q:q['prior'][1].__setitem__('x','healthy'),
            lambda q:q['likelihoods'][0]['weights'].pop('red'),
            lambda q:q['terminal_rewards'].pop(),
        ):
            q=req();mutate(q)
            with self.subTest(query=str(q)[:120]),self.assertRaises(AppError):parse_belief(q)

    def test_invalid_float_boolean_negative_prior_and_size(self):
        for key,value in [('mass','-1/2'),('mass',True),('mass',.5),('mass','1/'+'9'*300)]:
            q=req();q['prior'][0][key]=value
            with self.subTest(value=value),self.assertRaises(AppError):parse_belief(q)

    def test_non_singleton_strategic_state_rejected(self):
        q=req();q['model']['states']['strategic'].append('t')
        with self.assertRaises(AppError):parse_belief(q)

    def test_stale_receipt_cannot_change_original_likelihood_or_transition(self):
        q=req();r=propose_belief(q)
        a=deepcopy(q)
        a['likelihoods'][0]['weights']={'green':'1/2','red':'1/2','unseen':'0'}
        with self.assertRaises(AppError):check_belief(a,r)
        a=deepcopy(q)
        for row in a['model']['P']:
            if row['x']=='healthy' and row['a']=='repair':row['weights']={'healthy':'1','damaged':'0'}
        with self.assertRaises(AppError):check_belief(a,r)

    def test_receipt_must_not_launder_hidden_policy_into_observation_policy(self):
        q=req();r=propose_belief(q)
        r['policy'][0]['selected_action']='repair'
        with self.assertRaises(AppError):check_belief(q,r)

    def test_false_unreachable_posterior_rejected(self):
        q=req();r=propose_belief(q)
        r['policy'][2]['posterior']=['1/2','1/2']
        with self.assertRaises(AppError):check_belief(q,r)

    def test_alternative_tied_policy_accepts_when_result_law_matches(self):
        q=req()
        for x in q['terminal_rewards']:x['value']='0'
        r=propose_belief(q)
        self.assertEqual(check_belief(q,r)['status'],'PASS')
        for line in r['policy']:
            if line['observation'] in ('green','red'):line['selected_action']='repair'
        r['next_world_law']=['3/4','1/4']
        self.assertEqual(r['optimal_expected_terminal_reward'],'0')
        self.assertEqual(check_belief(q,r)['status'],'PASS')

    def test_zero_prior_hidden_state_does_not_restrict_reachable_action(self):
        q=req()
        q['prior']=[{'x':'healthy','mass':'1'},{'x':'damaged','mass':'0'}]
        q['model']['feasible']=[{'s':'s','x':'healthy','actions':['leave','repair']},
                                {'s':'s','x':'damaged','actions':['repair']}]
        q['model']['alpha'][1]['weights']={'leave':'0','repair':'1'}
        q['model']['P']=[row for row in q['model']['P'] if row['x']=='healthy' or row['a']=='repair']
        q['model']['U']=[row for row in q['model']['U'] if row['x']=='healthy' or row['a']=='repair']
        receipt=propose_belief(q)
        self.assertEqual(check_belief(q,receipt)['status'],'PASS')
        for row in receipt['policy'][:2]:
            self.assertEqual(row['posterior'],['1','0'])
            self.assertEqual(row['available_actions'],['leave','repair'])
        self.assertIsNone(receipt['policy'][2]['selected_action'])

    def test_source_alpha_identity_is_bound_but_not_treated_as_observation_policy(self):
        q=req();original=propose_belief(q)
        revised=deepcopy(q)
        revised['model']['alpha'][0]['weights']={'leave':'0','repair':'1'}
        with self.assertRaises(AppError):check_belief(revised,original)
        rebuilt=propose_belief(revised)
        self.assertNotEqual(original['source_model_identity'],rebuilt['source_model_identity'])
        self.assertEqual(original['policy'],rebuilt['policy'])
        self.assertEqual(original['optimal_expected_terminal_reward'],rebuilt['optimal_expected_terminal_reward'])
        self.assertEqual(check_belief(revised,rebuilt)['status'],'PASS')

    def test_zero_reward_and_negative_reward_tied_optima_still_verified(self):
        q=req()
        for item in q['terminal_rewards']:item['value']='-1'
        receipt=propose_belief(q)
        self.assertEqual(receipt['optimal_expected_terminal_reward'],'-1')
        self.assertEqual(receipt['best_blind_policy_reward'],'-1')
        self.assertEqual(receipt['value_of_observation'],'0')
        self.assertEqual(check_belief(q,receipt)['status'],'PASS')
        receipt['policy'][0]['selected_action']='repair'
        receipt['policy'][1]['selected_action']='repair'
        receipt['next_world_law']=['3/4','1/4']
        self.assertEqual(check_belief(q,receipt)['status'],'PASS')

    def test_tamper_all_material_calculation_fields(self):
        q=req();r=propose_belief(q)
        mutants=[
            ('value',lambda z:z.__setitem__('optimal_expected_terminal_reward','1')),
            ('blind',lambda z:z.__setitem__('best_blind_policy_reward','1')),
            ('information',lambda z:z.__setitem__('value_of_observation','0')),
            ('law',lambda z:z['next_world_law'].__setitem__(0,'1')),
            ('posterior',lambda z:z['policy'][0]['posterior'].__setitem__(0,'1')),
            ('likelihood',lambda z:z['likelihood_matrix'][0].__setitem__(0,'1')),
            ('wrong_ties',lambda z:z['policy'][0]['tied_max_actions'].__setitem__(0,'repair')),
            ('source',lambda z:z['source_model_identity'].__setitem__('sha256','0'*64)),
            ('fake_proof',lambda z:z.__setitem__('lean_status','PASSED')),
            ('fake_science',lambda z:z.__setitem__('scientific_claims_verified',True)),
            ('extra_approval',lambda z:z.__setitem__('publication_approved',True)),
        ]
        for label,mutate in mutants:
            with self.subTest(label=label),self.assertRaises(AppError):
                x=deepcopy(r);mutate(x);check_belief(q,x)

if __name__=='__main__':unittest.main()
