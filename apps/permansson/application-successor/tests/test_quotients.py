"""Type-respecting finite induced-kernel quotients, exact transport and adversaries."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction
from pathlib import Path
import sys,unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.engines.quotients import propose_quotient,parse_quotient
from permansson_app.receipts.quotients import check_quotient
from permansson_app.errors import AppError
from test_grammar import model as fixture_model


def sample():
    baseline=fixture_model()
    alpha=deepcopy(baseline)
    for row in alpha['alpha']:
        if row['x']=='safe':row['weights']={'stay':'0','switch':'1'}
    u=deepcopy(baseline)
    for row in u['U']:
        if row['s']=='s0' and row['x']=='safe' and row['a']=='stay' and row['xp']=='safe':
            row['weights']={'s0':'0','s1':'1'}
    return {'format':'Permansson.App.FiniteTypedQuotientRequest.v1',
      'baseline':baseline,
      'interventions':[{'id':'alpha_all','target':'alpha','model':alpha},
                       {'id':'update_state','target':'U','model':u}],
      'quotient':{'strategic_states':['q'],'world_states':['safe','outside'],
        'strategic_map':{'s0':'q','s1':'q'},
        'world_map':{'safe':'safe','outside':'outside'}},
      'region':[['s0','safe'],['s1','safe']],
      'comparison_states':[['s0','safe'],['s1','safe']],
      'horizon':1,'value_type':'survival_horizon'}


class QuotientTests(unittest.TestCase):
 def test_true_nonidentity_projection_preserves_all_declared_laws(self):
    raw=sample();receipt=propose_quotient(raw)
    self.assertEqual(check_quotient(raw,receipt)['status'],'PASS')
    self.assertEqual(receipt['fine_to_coarse_indices'],[0,1,0,1])
    self.assertEqual(receipt['profiles'][0]['coarse_kernel'],[['1','0'],['0','1']])
    self.assertEqual(receipt['profiles'][1]['coarse_kernel'],[['0','1'],['0','1']])
    self.assertEqual(receipt['profiles'][2]['coarse_kernel'],[['1','0'],['0','1']])
    self.assertEqual(receipt['profiles'][0]['coarse_values'],['1'])
    self.assertEqual(receipt['effects'][0]['fine_differences'],['-1','-1'])
    self.assertEqual(receipt['effects'][1]['coarse_differences'],['0'])
    self.assertEqual(receipt['lean_status'],'NOT_EXECUTED')
    self.assertFalse(receipt['scientific_claims_verified'])
 def test_unlumpable_baseline_rejected(self):
    raw=sample();raw['baseline']['alpha'][0]['weights']={'stay':'0','switch':'1'}
    # Retain held-fixed baseline/intervened P; first fail can be from stale model P
    for i in raw['interventions']:
      i['model']['alpha'][0]['weights']={'stay':'0','switch':'1'}
    with self.assertRaisesRegex(AppError,'lumpab'):
      propose_quotient(raw)
 def test_single_intervention_breaks_lumpability_even_when_baseline_lumpable(self):
    raw=sample();raw['interventions'][0]['model']['alpha'][2]['weights']={'stay':'1','switch':'0'}
    with self.assertRaisesRegex(AppError,'lumpab'):propose_quotient(raw)
 def test_held_fixed_physical_transition_mutation_fails(self):
    raw=sample();r=raw['interventions'][0]['model']['P'][0]
    r['weights']={'safe':'0','outside':'1'}
    with self.assertRaises(AppError):propose_quotient(raw)
 def test_comparison_full_fiber_required(self):
    raw=sample();raw['comparison_states']=[['s0','safe']]
    with self.assertRaisesRegex(AppError,'fiber'):propose_quotient(raw)
 def test_region_full_fiber_required(self):
    raw=sample();raw['region']=[['s0','safe']]
    with self.assertRaisesRegex(AppError,'fiber'):propose_quotient(raw)
 def test_zero_horizon_both_values_one(self):
    raw=sample();raw['horizon']=0
    r=propose_quotient(raw)
    self.assertEqual(r['profiles'][0]['fine_values'],['1','1'])
    self.assertEqual(r['effects'][0]['coarse_differences'],['0'])
    self.assertEqual(check_quotient(raw,r)['status'],'PASS')
 def test_exit_complements_survival(self):
    raw=sample();raw['value_type']='exit_by_horizon'
    r=propose_quotient(raw)
    self.assertEqual(r['profiles'][0]['coarse_values'],['0'])
    self.assertEqual(r['profiles'][1]['coarse_values'],['1'])
    self.assertEqual(check_quotient(raw,r)['status'],'PASS')
 def test_ontological_projection_only_no_false_alpha_P_U_status(self):
    r=propose_quotient(sample())
    self.assertIn('NOT_COARSE_ALPHA_P_U',r['verified_law_scope'])
    self.assertIn('NOT_EXACT_GR_PR',r['claim_scope'])
 def test_wrong_quotient_kernel_rejected(self):
    raw=sample();r=propose_quotient(raw)
    r['profiles'][1]['coarse_kernel'][0]=['1','0']
    with self.assertRaises(AppError):check_quotient(raw,r)
 def test_wrong_effect_rejected(self):
    raw=sample();r=propose_quotient(raw)
    r['effects'][0]['coarse_differences']=['0']
    with self.assertRaises(AppError):check_quotient(raw,r)
 def test_source_swap_rejected(self):
    raw=sample();r=propose_quotient(raw)
    raw['baseline']['alpha'][2]['weights']={'stay':'0','switch':'1'}
    with self.assertRaises(AppError):check_quotient(raw,r)
 def test_numeric_bool_impersonation_rejected(self):
    raw=sample();r=propose_quotient(raw)
    r['horizon']=True
    with self.assertRaises(AppError):check_quotient(raw,r)
 def test_status_impersonation_rejected(self):
    raw=sample();r=propose_quotient(raw)
    r['lean_status']='PROVED'
    with self.assertRaises(AppError):check_quotient(raw,r)
 def test_projection_must_be_onto(self):
    raw=sample();raw['quotient']['strategic_states']=['q','unused']
    with self.assertRaises(AppError):parse_quotient(raw)
 def test_identity_quotient_rejected(self):
    raw=sample();raw['quotient']={'strategic_states':['s0','s1'],'world_states':['safe','outside'],
          'strategic_map':{'s0':'s0','s1':'s1'},'world_map':{'safe':'safe','outside':'outside'}}
    with self.assertRaises(AppError):parse_quotient(raw)
 def test_wrong_comparison_beyond_region(self):
    raw=sample();raw['comparison_states']=[['s0','outside'],['s1','outside']]
    with self.assertRaises(AppError):parse_quotient(raw)
 def test_unreported_treated_model_mutation_rejected(self):
    raw=sample();raw['interventions'][1]['model']['alpha'][0]['weights']={'stay':'0','switch':'1'}
    with self.assertRaises(AppError):propose_quotient(raw)
 def test_request_boolean_horizon_rejected(self):
    raw=sample();raw['horizon']=True
    with self.assertRaises(AppError):propose_quotient(raw)

if __name__=='__main__':unittest.main()
