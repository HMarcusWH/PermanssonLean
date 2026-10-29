"""Typed finite patch grammar, independent original-model and minimality checks."""
from __future__ import annotations
import copy
import sys
import unittest
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.engines.grammar import propose_grammar,parse_grammar,apply_block
from permansson_app.receipts.grammar import check_grammar
from permansson_app.errors import AppError


def model():
    ss=['s0','s1'];xx=['safe','outside'];aa=['stay','switch']
    return {'format':'Permansson.App.FiniteStrategicWorld.v1',
       'states':{'strategic':ss,'world':xx,'actions':aa},
       'feasible':[{'s':s,'x':x,'actions':aa.copy()} for s in ss for x in xx],
       'alpha':[{'s':s,'x':x,'weights':{'stay':'1','switch':'0'}} for s in ss for x in xx],
       'P':[{'s':s,'x':x,'a':a,'weights':{'safe':('1' if x=='safe' and a=='stay' else '0'),
            'outside':('0' if x=='safe' and a=='stay' else '1')}}
            for s in ss for x in xx for a in aa],
       'U':[{'s':s,'x':x,'a':a,'xp':xp,'weights':{'s0':('1' if s=='s0' else '0'),
             's1':('1' if s=='s1' else '0')}}
            for s in ss for x in xx for a in aa for xp in xx]}


def request(admitted=None,corners=True):
    if admitted is None:admitted=[[],['a'],['u'],['a','u']]
    return {'format':'Permansson.App.FiniteGrammarRequest.v1',
      'baseline':model(),
      'patches':[{'id':'a','target':'alpha','rows':[
        {'s':'s0','x':'safe','weights':{'stay':'0','switch':'1'}}]},
        {'id':'u','target':'U','rows':[
        {'s':'s0','x':'safe','a':'stay','xp':'safe','weights':{'s0':'0','s1':'1'}}]}],
      'admitted_blocks':admitted,
      'region':[['s0','safe']], 'comparison_states':[['s0','safe']],
      'horizon':1,'value_type':'exit_by_horizon',
      'four_corners':[{'alpha_component':'a','U_component':'u'}] if corners else []}


class GrammarTests(unittest.TestCase):
 def test_two_incomparable_minimal_positive_blocks(self):
    raw=request();receipt=propose_grammar(raw)
    self.assertEqual(check_grammar(raw,receipt)['status'],'PASS')
    self.assertEqual(receipt['minimal_positive_blocks'],[['a'],['u']])
    self.assertEqual([r['values_by_comparison_state'] for r in receipt['block_results']],
                     [['0'],['1'],['1'],['1']])
    self.assertEqual(receipt['four_corners'][0]['interactions_by_comparison_state'],['-1'])
    self.assertFalse(receipt['scientific_claims_verified'])
 def test_joint_admitted_without_either_singleton(self):
    raw=request([[],['a','u']],corners=False)
    receipt=propose_grammar(raw)
    self.assertEqual(receipt['minimal_positive_blocks'],[['a','u']])
    self.assertEqual(check_grammar(raw,receipt)['status'],'PASS')
    with self.assertRaises(AppError):apply_block(parse_grammar(raw),('a',))
 def test_mismatched_patch_overlap_rejected(self):
    raw=request(corners=False)
    raw['patches'].append({'id':'b','target':'alpha',
        'rows':[{'s':'s0','x':'safe','weights':{'stay':'1','switch':'0'}}]})
    raw['admitted_blocks'].append(['a','b'])
    with self.assertRaises(AppError):propose_grammar(raw)
 def test_equal_patch_overlap_is_compatible(self):
    raw=request(admitted=[[],['a','b']],corners=False)
    raw['patches'].append({'id':'b','target':'alpha',
        'rows':[{'s':'s0','x':'safe','weights':{'stay':'0','switch':'1'}}]})
    result=propose_grammar(raw)
    self.assertEqual(check_grammar(raw,result)['status'],'PASS')
    self.assertEqual(result['minimal_positive_blocks'],[['a','b']])
 def test_missing_original_baseline_block_rejected(self):
    raw=request([['a'],['u']],corners=False)
    with self.assertRaises(AppError):propose_grammar(raw)
 def test_missing_singleton_four_corner_rejected(self):
    raw=request([[],['a','u']],corners=True)
    with self.assertRaises(AppError):propose_grammar(raw)
 def test_fake_treated_value_rejected(self):
    raw=request();r=propose_grammar(raw)
    r['block_results'][1]['values_by_comparison_state']=['0']
    with self.assertRaises(AppError):check_grammar(raw,r)
 def test_hidden_positive_block_rejected(self):
    raw=request();r=propose_grammar(raw)
    r['minimal_positive_blocks']=[['a']]
    with self.assertRaises(AppError):check_grammar(raw,r)
 def test_changed_interaction_rejected(self):
    raw=request();r=propose_grammar(raw)
    r['four_corners'][0]['interactions_by_comparison_state']=['0']
    with self.assertRaises(AppError):check_grammar(raw,r)
 def test_horizon_boolean_masquerade_rejected(self):
    raw=request();r=propose_grammar(raw)
    r['horizon']=True
    with self.assertRaises(AppError):check_grammar(raw,r)
 def test_false_lean_status_rejected(self):
    raw=request();r=propose_grammar(raw)
    r['lean_status']='CERTIFIED'
    with self.assertRaises(AppError):check_grammar(raw,r)
 def test_wrong_component_order_rejected(self):
    raw=request([[],['u','a']],corners=False)
    with self.assertRaises(AppError):propose_grammar(raw)
 def test_invalid_probabilities_rejected(self):
    raw=request();raw['patches'][0]['rows'][0]['weights']['stay']='1/2'
    with self.assertRaises(AppError):propose_grammar(raw)
 def test_unknown_physical_patch_target_rejected(self):
    raw=request();raw['patches'][0]['target']='P'
    with self.assertRaises(AppError):propose_grammar(raw)

if __name__=='__main__':unittest.main()
