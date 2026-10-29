"""Exact source/timing/receipt adversaries for the finite nature chronology."""
from __future__ import annotations
import copy
import json
from pathlib import Path
import random
import sys
import unittest
from fractions import Fraction
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.robust_nature import parse_nature,propose_nature
from permansson_app.receipts.robust_nature import check_nature
from permansson_app.finite_world import exact_ratio

EXAMPLE=Path(__file__).resolve().parents[1]/'src/permansson_app/data/examples/robust_nature.v1.json'


def request(): return json.loads(EXAMPLE.read_text())


class NatureChronologyTests(unittest.TestCase):
    def test_actual_two_step_separation_and_action_optimum(self):
        raw=request();receipt=propose_nature(raw)
        self.assertEqual(check_nature(raw,receipt)['status'],'PASS')
        self.assertEqual(receipt['comparison']['fixed_rectangular'],['0','0'])
        self.assertEqual(receipt['comparison']['fixed_committed_worst'],['1','0'])
        self.assertEqual(receipt['comparison']['fixed_rectangular_minus_committed'],['-1','0'])
        self.assertEqual(receipt['comparison']['rectangular_optimized'],['1','1'])
        # At horizon 2 both 'go' and 'safe' are optimal at start.
        self.assertEqual(receipt['rectangular_argmax_by_remaining'][2][0],['go','safe'])
        self.assertEqual(receipt['rectangular_minimizers_by_action'][1][1]['go'],['theta_good_second'])
        self.assertFalse(receipt['scientific_claims_verified'])
        self.assertEqual(receipt['lean_status'],'NOT_EXECUTED')
        self.assertEqual(receipt['committed_scope'],'declared_fixed_policy_only_not_committed_game_optimum')

    def test_horizon_zero_terminal_reward_is_exact(self):
        raw=request();raw['horizon']=0
        result=propose_nature(raw)
        self.assertEqual(check_nature(raw,result)['status'],'PASS')
        self.assertEqual(result['comparison']['fixed_rectangular'],['0','0'])
        self.assertEqual(result['comparison']['fixed_committed_worst'],['0','0'])
        self.assertEqual(len(result['rectangular_optimal_values_by_remaining']),1)

    def test_single_nature_model_equality_for_fixed_policy(self):
        raw=request();raw['nature_models']=raw['nature_models'][:1]
        result=propose_nature(raw)
        self.assertEqual(check_nature(raw,result)['status'],'PASS')
        self.assertEqual(result['comparison']['fixed_rectangular_minus_committed'],['0','0'])

    def test_horizon_one_requires_newer_control(self):
        raw=request();raw['horizon']=1
        result=propose_nature(raw)
        self.assertEqual(check_nature(raw,result)['status'],'PASS')
        self.assertEqual(result['comparison']['rectangular_optimized'],['1','1'])
        self.assertEqual(result['comparison']['fixed_rectangular'],['0','0'])

    def test_negative_terminal_reward_not_probability(self):
        raw=request();raw['terminal_rewards'][-1]['value']='-1/2'
        result=propose_nature(raw)
        self.assertEqual(check_nature(raw,result)['status'],'PASS')
        self.assertEqual(result['comparison']['fixed_rectangular'][0],'-1/2')

    def test_reordered_scenario_ids_are_bound(self):
        raw=request();old=propose_nature(raw)
        raw['nature_models'].reverse()
        altered=propose_nature(raw)
        self.assertEqual(check_nature(raw,altered)['status'],'PASS')
        self.assertNotEqual(old['request_identity'],altered['request_identity'])
        with self.assertRaises(AppError):check_nature(raw,old)

    def test_input_foreign_P_row(self):
        raw=request();raw['nature_models'][0]['P'][0]['x']='unknown'
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_missing_P_row(self):
        raw=request();raw['nature_models'][0]['P'].pop()
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_duplicate_P_row(self):
        raw=request();raw['nature_models'][0]['P'][0]=copy.deepcopy(raw['nature_models'][0]['P'][1])
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_changed_P_probability_not_normalized(self):
        raw=request();raw['nature_models'][0]['P'][0]['weights']['start']='1'
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_illegal_policy_action(self):
        raw=request();raw['fixed_policy'][0]['action']='unknown'
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_missing_policy_state(self):
        raw=request();raw['fixed_policy'].pop()
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_duplicate_policy_state(self):
        raw=request();raw['fixed_policy'][0]=copy.deepcopy(raw['fixed_policy'][1])
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_duplicate_model_id(self):
        raw=request();raw['nature_models'][1]['id']=raw['nature_models'][0]['id']
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_unknown_comparison_state(self):
        raw=request();raw['comparison_states']=[['memory','alien']]
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_duplicate_comparison_state(self):
        raw=request();raw['comparison_states']*=2
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_reward_gap(self):
        raw=request();raw['terminal_rewards'].pop()
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_float_or_bool_not_rational(self):
        raw=request();raw['terminal_rewards'][0]['value']=0.5
        with self.assertRaises(AppError):parse_nature(raw)
        raw=request();raw['horizon']=True
        with self.assertRaises(AppError):parse_nature(raw)

    def test_input_extra_fields_rejected(self):
        raw=request();raw['made_up_approval']=True
        with self.assertRaises(AppError):parse_nature(raw)
        raw=request();raw['nature_models'][0]['U']=raw['baseline']['U']
        with self.assertRaises(AppError):parse_nature(raw)

    def test_all_critical_receipt_tampering_rejected(self):
        raw=request();base=propose_nature(raw)
        mutants=[
            ('fixed_policy_rectangular_values_by_remaining',lambda x:x[2].__setitem__(0,'1')),
            ('rectangular_optimal_values_by_remaining',lambda x:x[2].__setitem__(0,'0')),
            ('fixed_policy_committed_values_by_nature',lambda x:x[0][2].__setitem__(0,'0')),
            ('rectangular_argmax_by_remaining',lambda x:x[2][0].pop()),
            ('rectangular_minimizers_by_action',lambda x:x[1][1]['go'].append('theta_good_first')),
            ('fixed_policy_rectangular_minimizers',lambda x:x[1][1].clear()),
            ('nature_model_identities',lambda x:x.reverse()),
            ('terminal_rewards',lambda x:x.__setitem__(0,'1')),
            ('fixed_policy_actions',lambda x:x.__setitem__(0,'safe')),
            ('comparison',lambda x:x['fixed_committed_worst'].__setitem__(0,'0')),
        ]
        for name,mutate in mutants:
            with self.subTest(name=name):
                receipt=copy.deepcopy(base)
                mutate(receipt[name])
                with self.assertRaises(AppError):check_nature(raw,receipt)

    def test_fake_boolean_certification_rejected(self):
        raw=request();receipt=propose_nature(raw)
        receipt['scientific_claims_verified']=True
        with self.assertRaises(AppError):check_nature(raw,receipt)
        receipt=propose_nature(raw);receipt['strategic_alpha_and_U_held_fixed']=1
        with self.assertRaises(AppError):check_nature(raw,receipt)

    def test_omitted_and_extra_receipt_fields_rejected(self):
        raw=request();receipt=propose_nature(raw)
        del receipt['nature_timing']
        with self.assertRaises(AppError):check_nature(raw,receipt)
        receipt=propose_nature(raw);receipt['independent_certified']=True
        with self.assertRaises(AppError):check_nature(raw,receipt)

    def test_fixed_policy_per_model_direct_path_enumeration(self):
        # Recompute P(theta) trajectories explicitly without either value solver.
        raw=request();q=parse_nature(raw);receipt=propose_nature(raw)
        start=q.states.index(('memory','start'))
        for theta,world in enumerate(q.nature_worlds):
            atoms=[(start,Fraction(1))]
            for _ in range(q.horizon):
                expanded=[]
                for i,mass in atoms:
                    s,x=q.states[i];a=q.policy[i]
                    for j,(sp,xp) in enumerate(q.states):
                        prob=world.P[s,x,a][world.world.index(xp)]*world.U[s,x,a,xp][world.strategic.index(sp)]
                        if prob:expanded.append((j,mass*prob))
                atoms=expanded
            value=sum((mass*q.rewards[i] for i,mass in atoms),Fraction(0))
            self.assertEqual(exact_ratio(receipt['fixed_policy_committed_values_by_nature'][theta][-1][start]),value)

    def test_random_probabilities_against_second_checker(self):
        rng=random.Random(41)
        for _ in range(12):
            raw=request()
            for model in raw['nature_models']:
                for row in model['P']:
                    a,b=rng.randint(0,4),rng.randint(0,4)
                    den=5
                    # Mix 2 targets, still a proper stochastic row.
                    target1,target2=raw['baseline']['states']['world'][:2]
                    row['weights']={x:('1' if a==5 and x==target1 else
                                        str(Fraction(a,den)) if x==target1 else
                                        str(Fraction(den-a,den)) if x==target2 else '0')
                                    for x in raw['baseline']['states']['world']}
            raw['horizon']=rng.randint(1,4)
            out=propose_nature(raw)
            self.assertEqual(check_nature(raw,out)['status'],'PASS')
            for x,y in zip(out['comparison']['fixed_rectangular'],out['comparison']['fixed_committed_worst']):
                self.assertLessEqual(exact_ratio(x),exact_ratio(y))

if __name__=='__main__':unittest.main()
