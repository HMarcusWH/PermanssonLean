"""Exact one-stage private-control saddle receipts: values, timing and adversaries."""
from __future__ import annotations
import copy
import json
from pathlib import Path
import sys
import unittest
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'src'))
from permansson_app.errors import AppError
from permansson_app.engines.private_stage import propose_private_stage
from permansson_app.receipts.private_stage import check_private_stage

EXAMPLE=Path(__file__).resolve().parents[1]/'src/permansson_app/data/examples/private_stage.v1.json'


def request():
    return json.loads(EXAMPLE.read_text())


def game(controls,nature,payoff):
    return {'format':'Permansson.App.PrivateStageRequest.v1',
            'labels':{'controls':controls,'nature':nature},'payoff':payoff}


class PrivateStageTests(unittest.TestCase):
    def test_example_saddle_and_randomization_gain(self):
        raw=request();receipt=propose_private_stage(raw)
        check=check_private_stage(raw,receipt)
        self.assertEqual(check['status'],'PASS')
        self.assertEqual(receipt['value'],'1')
        self.assertEqual(receipt['controller_mixture'],['1/2','1/2','0'])
        self.assertEqual(receipt['nature_mixture'],['3/5','2/5'])
        self.assertEqual(receipt['controller_guarantee_by_nature'],['1','1'])
        self.assertEqual(receipt['nature_hold_by_control'],['1','1','1/2'])
        # The safe pure control is worth only 1/2: randomizing privately gains 1/2.
        self.assertEqual(receipt['pure_control_value'],'1/2')
        self.assertEqual(receipt['pure_maxmin_controls'],['hold'])
        self.assertEqual(receipt['randomization_gain'],'1/2')
        self.assertEqual(receipt['timing'],'NATURE_SEES_MIXTURE_NOT_REALIZED_CONTROL')

    def test_matching_pennies_matches_research_fixture(self):
        # Research's MatchingFixture: private value 1/2, every pure control 0.
        raw=game(['heads','tails'],['heads','tails'],[['1','0'],['0','1']])
        receipt=propose_private_stage(raw)
        self.assertEqual((receipt['value'],receipt['pure_control_value']),('1/2','0'))
        self.assertEqual(receipt['controller_mixture'],['1/2','1/2'])

    def test_negative_constant_payoff(self):
        # Research's negative fixture: the value coordinate may be negative.
        raw=game(['a','b'],['x','y'],[['-7','-7'],['-7','-7']])
        receipt=propose_private_stage(raw)
        self.assertEqual(check_private_stage(raw,receipt)['status'],'PASS')
        self.assertEqual((receipt['value'],receipt['randomization_gain']),('-7','0'))

    def test_rock_paper_scissors_and_single_parameter(self):
        rps=game(['r','p','s'],['r','p','s'],[['0','1','-1'],['-1','0','1'],['1','-1','0']])
        receipt=propose_private_stage(rps)
        self.assertEqual(receipt['value'],'0')
        self.assertEqual(receipt['controller_mixture'],['1/3','1/3','1/3'])
        self.assertEqual(receipt['pure_control_value'],'-1')
        # One nature parameter: the best pure control is optimal.
        one=game(['a','b','c'],['x'],[['1','-2','3']])
        receipt=propose_private_stage(one)
        self.assertEqual((receipt['value'],receipt['randomization_gain']),('3','0'))
        self.assertEqual(receipt['controller_mixture'],['0','0','1'])

    def test_four_by_four_certificate(self):
        raw=game(['a','b','c','d'],['w','x','y','z'],
                 [['1','-2','3','0'],['-1','2','-3','1'],['2','1','0','-1'],['0','0','1','2']])
        receipt=propose_private_stage(raw)
        self.assertEqual(check_private_stage(raw,receipt)['status'],'PASS')
        self.assertEqual(receipt['value'],'5/18')
        self.assertEqual(receipt['randomization_gain'],'23/18')

    def test_suboptimal_or_false_certificates_rejected(self):
        raw=request();receipt=propose_private_stage(raw)
        for key,value in (('value','11/10'),('value','1/2'),('controller_mixture',['1','0','0']),
                          ('controller_mixture',['1/2','1/4','1/4']),('nature_mixture',['1/2','1/2']),
                          ('nature_mixture',['3/5','3/5']),('pure_control_value','1'),
                          ('pure_maxmin_controls',['calm']),('randomization_gain','0'),
                          ('timing','NATURE_SEES_REALIZED_CONTROL'),('lean_status','PASS'),
                          ('scientific_claims_verified',True)):
            bad=copy.deepcopy(receipt);bad[key]=value
            with self.subTest(key=key,value=value),self.assertRaises(AppError):
                check_private_stage(raw,bad)
        bad=copy.deepcopy(receipt);bad['extra']=1
        with self.assertRaises(AppError):check_private_stage(raw,bad)

    def test_receipt_for_a_different_payoff_rejected(self):
        raw=request();receipt=propose_private_stage(raw)
        other=copy.deepcopy(raw);other['payoff'][0][1]='0'
        with self.assertRaises(AppError):check_private_stage(other,receipt)

    def test_input_scope(self):
        for mutate in (lambda r:r['labels']['controls'].append('x'),        # payoff width mismatch
                       lambda r:r['payoff'].pop(),                            # missing nature row
                       lambda r:r['payoff'][0].__setitem__(0,'0.5'),          # non-canonical rational
                       lambda r:r['labels']['nature'].__setitem__(1,'dry'),   # duplicate label
                       lambda r:r.__setitem__('format','other'),
                       lambda r:r.__setitem__('extra',1)):
            raw=request();mutate(raw)
            with self.assertRaises(AppError):propose_private_stage(raw)
        raw=game(list('abcde'),['x'],[['1']*5])
        with self.assertRaises(AppError):propose_private_stage(raw)


if __name__=='__main__':
    unittest.main()
