"""Independent finite belief-tree tests, chronology and tamper boundaries."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction
from itertools import product
from pathlib import Path
import json,sys,unittest
APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.engines.belief_tree import propose_belief_tree,parse_belief_tree
from permansson_app.receipts.belief_tree import check_belief_tree
from permansson_app.engines.belief import propose_belief
from permansson_app.errors import AppError

FIX=APP/'src/permansson_app/data/examples/belief_tree.v1.json'
ONE=APP/'src/permansson_app/data/examples/belief.v1.json'
def sample():return json.loads(FIX.read_text())


class BeliefTreeTests(unittest.TestCase):
 def test_two_stage_genuine_history_dependent_optimal_policy(self):
  raw=sample();r=propose_belief_tree(raw);checked=check_belief_tree(raw,r)
  self.assertEqual(checked['status'],'PASS')
  self.assertTrue(checked['terminal_law_from_actual_P_U'])
  self.assertEqual(r['horizon'],2)
  self.assertEqual(r['optimal_expected_terminal_reward'],'55/64')
  self.assertEqual(r['best_blind_action_sequence_reward'],'3/4')
  self.assertEqual(r['value_of_observation_history'],'7/64')
  tree=r['optimal_policy_tree']['observations']
  self.assertEqual(tree[0]['selected_action'],'leave')
  self.assertEqual(tree[1]['selected_action'],'leave') # legal tie, not future clairvoyance
  self.assertEqual(tree[0]['next_tree']['observations'][0]['selected_action'],'leave')
  self.assertEqual(tree[1]['next_tree']['observations'][0]['selected_action'],'repair')
  self.assertEqual(tree[2]['observation_probability'],'0')
  self.assertIsNone(tree[2]['next_tree'])
  self.assertEqual(sum(map(Fraction,r['terminal_joint_law'])),1)
  self.assertFalse(r['scientific_claims_verified'])
  self.assertEqual(r['lean_status'],'NOT_EXECUTED')

 def test_independent_exhaustive_brute_force_64_policy_trees(self):
  # Direct summation over hidden trajectories and observation histories,
  # with no call to either the producer's or checker's dynamic programming.
  q=sample()
  probs={r['x']:Fraction(r['mass']) for r in q['prior']}
  qs={r['x']:{k:Fraction(v) for k,v in r['weights'].items()} for r in q['likelihoods']}
  transition={(r['x'],r['a']):{k:Fraction(v) for k,v in r['weights'].items()} for r in q['model']['P']}
  rewards={r['x']:Fraction(r['value']) for r in q['terminal_rewards']}
  history=['green','red']
  actions=['leave','repair']
  maximum=None
  for sequence in product(actions,repeat=6):
   root=dict(zip(history,sequence[:2]))
   second=dict(zip(product(history,history),sequence[2:]))
   value=Fraction(0)
   for x,p0 in probs.items():
    for o0 in history:
     a0=root[o0]
     for x1,p1 in transition[x,a0].items():
      for o1 in history:
       a1=second[o0,o1]
       for x2,p2 in transition[x1,a1].items():
        value+=p0*qs[x][o0]*p1*qs[x1][o1]*p2*rewards[x2]
   maximum=value if maximum is None else max(maximum,value)
  self.assertEqual(maximum,Fraction(55,64))
  self.assertEqual(Fraction(propose_belief_tree(q)['optimal_expected_terminal_reward']),maximum)

 def test_horizon_one_reproduces_one_step_exactly(self):
  one=json.loads(ONE.read_text());q=sample();q['horizon']=1
  r=propose_belief_tree(q)
  self.assertEqual(r['optimal_expected_terminal_reward'],propose_belief(one)['optimal_expected_terminal_reward'])
  self.assertEqual(r['value_of_observation_history'],propose_belief(one)['value_of_observation'])
  self.assertEqual(check_belief_tree(q,r)['status'],'PASS')

 def test_three_stage_bounded_policy_and_terminal_law(self):
  q=sample();q['horizon']=3
  r=propose_belief_tree(q)
  self.assertEqual(check_belief_tree(q,r)['status'],'PASS')
  self.assertGreaterEqual(Fraction(r['optimal_expected_terminal_reward']),Fraction(55,64))
  self.assertEqual(sum(map(Fraction,r['terminal_joint_law'])),1)

 def test_reachable_perfect_signal_support_may_have_disjoint_actions(self):
  q=sample();q['likelihoods']=[
   {'x':'healthy','weights':{'green':'1','red':'0','unseen':'0'}},
   {'x':'damaged','weights':{'green':'0','red':'1','unseen':'0'}}]
  q['model']['feasible']=[{'s':'s','x':'healthy','actions':['leave']},
                          {'s':'s','x':'damaged','actions':['repair']}]
  q['model']['alpha'][1]['weights']={'leave':'0','repair':'1'}
  q['model']['P']=[r for r in q['model']['P'] if (r['x']=='healthy' and r['a']=='leave') or (r['x']=='damaged' and r['a']=='repair')]
  q['model']['U']=[r for r in q['model']['U'] if (r['x']=='healthy' and r['a']=='leave') or (r['x']=='damaged' and r['a']=='repair')]
  # Repair maps damaged to healthy; second observation supports only leave.
  r=propose_belief_tree(q)
  self.assertEqual(check_belief_tree(q,r)['status'],'PASS')
  self.assertIsNone(r['best_blind_action_sequence_reward'])
  self.assertEqual(r['optimal_expected_terminal_reward'],'1')

 def test_two_strategic_states_actual_update_kernel_matters(self):
  q=sample();m=q['model'];m['states']['strategic']=['s','t']
  for field in ('feasible','alpha','P'):
   copies=deepcopy(m[field]);
   for row in copies:row['s']='t'
   m[field].extend(copies)
  m['U']=[]
  for s in ('s','t'):
   for x in m['states']['world']:
    for a in m['states']['actions']:
     for xp in m['states']['world']:
      target='t' if a=='repair' else s
      m['U'].append({'s':s,'x':x,'a':a,'xp':xp,'weights':{'s':'1' if target=='s' else '0','t':'1' if target=='t' else '0'}})
  q['prior']=[{'s':s,'x':x,'mass':'1/2' if s=='s' else '0'} for s in ('s','t') for x in m['states']['world']]
  q['terminal_rewards']=[{'s':s,'x':x,'value':'1' if s=='t' and x=='healthy' else '0'} for s in ('s','t') for x in m['states']['world']]
  r=propose_belief_tree(q)
  self.assertEqual(check_belief_tree(q,r)['status'],'PASS')
  q2=deepcopy(q)
  for row in q2['model']['U']:
   row['weights']={'s':'1','t':'0'}
  r2=propose_belief_tree(q2)
  self.assertEqual(check_belief_tree(q2,r2)['status'],'PASS')
  self.assertNotEqual(r['optimal_expected_terminal_reward'],r2['optimal_expected_terminal_reward'])
  with self.assertRaises(AppError):check_belief_tree(q2,r)

 def test_missing_row_duplicate_bad_probability_and_noncanonical_json(self):
  for changer in (
   lambda q:q['prior'].pop(),
   lambda q:q['prior'][1].__setitem__('x','healthy'),
   lambda q:q['likelihoods'][1]['weights'].__setitem__('green','1/2'),
   lambda q:q['likelihoods'][0]['weights'].__setitem__('red',True),
   lambda q:q['terminal_rewards'].append(q['terminal_rewards'][0]),
   lambda q:q['observations'].append('green'),
   lambda q:q.__setitem__('future_hidden_state','healthy'),
   lambda q:q['prior'][0].__setitem__('mass','1/'+'9'*300),
  ):
   q=sample();changer(q)
   with self.subTest(changer=changer),self.assertRaises(AppError):parse_belief_tree(q)

 def test_horizon_bool_zero_and_four_rejected(self):
  for horizon in (False,True,0,4,-1,1.5,'2'):
   q=sample();q['horizon']=horizon
   with self.subTest(h=horizon),self.assertRaises(AppError):parse_belief_tree(q)

 def test_tamper_nested_history_or_undeclared_authority_fails(self):
  q=sample();expected=propose_belief_tree(q)
  mutants=[
   lambda r:r.__setitem__('optimal_expected_terminal_reward','1'),
   lambda r:r.__setitem__('value_of_observation_history','1'),
   lambda r:r['optimal_policy_tree']['observations'][0].__setitem__('selected_action','repair'),
   lambda r:r['optimal_policy_tree']['observations'][0]['next_prior'].__setitem__(0,'0'),
   lambda r:r['optimal_policy_tree']['observations'][0]['next_tree']['observations'][0].__setitem__('selected_action','repair'),
   lambda r:r['optimal_policy_tree']['observations'][0]['next_tree']['observations'][0].__setitem__('terminal_joint_law',None),
   lambda r:r['optimal_policy_tree']['observations'][2].__setitem__('posterior',['1','0']),
   lambda r:r['optimal_policy_tree'].__setitem__('remaining_transitions',1),
   lambda r:r['terminal_joint_law'].__setitem__(0,'0'),
   lambda r:r['likelihood_matrix'][0].__setitem__(0,'1'),
   lambda r:r.__setitem__('lean_status','PASSED'),
   lambda r:r.__setitem__('scientific_claims_verified',True),
   lambda r:r.__setitem__('kernel_checked_proof',True),
  ]
  for mutation in mutants:
   r=deepcopy(expected);mutation(r)
   with self.subTest(mutation=mutation),self.assertRaises(AppError):check_belief_tree(q,r)

 def test_source_alpha_and_probability_preservation(self):
  q=sample();r=propose_belief_tree(q)
  q2=deepcopy(q)
  q2['model']['alpha'][0]['weights']={'leave':'0','repair':'1'}
  q3=deepcopy(q)
  q3['likelihoods'][0]['weights']={'green':'1/2','red':'1/2','unseen':'0'}
  for mutated in (q2,q3):
   with self.assertRaises(AppError):check_belief_tree(mutated,r)
  rr=propose_belief_tree(q2)
  self.assertEqual(r['optimal_expected_terminal_reward'],rr['optimal_expected_terminal_reward'])
  self.assertNotEqual(r['source_model_identity'],rr['source_model_identity'])
  self.assertEqual(check_belief_tree(q2,rr)['status'],'PASS')

 def test_tied_and_negative_rewards(self):
  q=sample()
  for row in q['terminal_rewards']:row['value']='-1'
  r=propose_belief_tree(q)
  self.assertEqual(r['optimal_expected_terminal_reward'],'-1')
  self.assertEqual(r['value_of_observation_history'],'0')
  self.assertEqual(check_belief_tree(q,r)['status'],'PASS')

if __name__=='__main__':unittest.main()
