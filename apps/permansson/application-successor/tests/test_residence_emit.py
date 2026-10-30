"""Source-bound residence Lean candidates (all three modes): binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_residence_live_lean.py; these tests need no Lean.
"""
from __future__ import annotations
from copy import deepcopy
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.engines.residence import solve_residence
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.residence_emit import FORMAT,MAX_HORIZON,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/residence.v1.json'


def problem(mode='retryable',dwell=1,deadline=2,semantics='entry_by'):
    S,X=['s0','s1'],['x0','x1']
    feasible={(s,x):['wait','push'] for s in S for x in X}
    feasible['s1','x0']=['wait']
    alpha={(s,x):{'wait':'1/2','push':'1/2'} for s in S for x in X}
    alpha['s1','x0']={'wait':'1','push':'0'}
    P={}
    for s in S:
        for x in X:
            P[s,x,'wait']={'x0':'1','x1':'0'} if x=='x0' else {'x0':'1/2','x1':'1/2'}
            P[s,x,'push']={'x0':'1/3','x1':'2/3'}
    def U(s,a):return {'s0':'1/2','s1':'1/2'} if a=='push' else {s:'1',('s1' if s=='s0' else 's0'):'0'}
    model={'format':'Permansson.App.FiniteStrategicWorld.v1',
           'states':{'strategic':S,'world':X,'actions':['wait','push']},
           'feasible':[{'s':s,'x':x,'actions':feasible[s,x]} for s in S for x in X],
           'alpha':[{'s':s,'x':x,'weights':alpha[s,x]} for s in S for x in X],
           'P':[{'s':s,'x':x,'a':a,'weights':P[s,x,a]} for s in S for x in X for a in feasible[s,x]],
           'U':[{'s':s,'x':x,'a':a,'xp':xp,'weights':U(s,a)} for s in S for x in X for a in feasible[s,x] for xp in X]}
    danger=[{'strategic':'s1','world':'x0'}] if mode=='avoid' else []
    return {'format':'Permansson.App.FiniteResidenceRequest.v1','model':model,
            'target':[{'strategic':'s0','world':'x1'},{'strategic':'s1','world':'x1'}],
            'danger':danger,'mode':mode,'deadline':deadline,'deadline_semantics':semantics,
            'dwell_transitions':dwell,'initial_law':[{'state':[s,x],'mass':'1/4'} for s in S for x in X]}


class ResidenceEmitTests(unittest.TestCase):
    def test_checked_retryable_values_emit_optimality_theorems(self):
        raw=problem()
        receipt=solve_residence(raw)
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertIn('boundControlSystem input options options_exact states_pos',source)
        self.assertIn('theorem receipt_checked : checkResidenceValues sys targetSet dwell latest values = true',source)
        self.assertIn('def dwell : ℕ := 1',source)
        self.assertIn('def latest : ℕ := 2',source)
        self.assertEqual(meta['theorem_names'],['options_exact','receipt_checked','optimal_residence_0',
            'optimal_residence_1','optimal_residence_2','optimal_residence_3'])
        self.assertEqual(meta['scope']['horizon'],3)
        self.assertEqual(meta['initial_law_mixture'],'NOT_REFLECTED_PER_START_VALUES_ONLY')
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_completion_by_maps_to_the_same_lean_event(self):
        # completion-by deadline 3 with dwell 1 means latest entry 2 over 3 transitions.
        source,meta=emit_source(problem(semantics='completion_by',deadline=3),
                                solve_residence(problem(semantics='completion_by',deadline=3)))
        self.assertIn('def latest : ℕ := 2',source)
        self.assertEqual(meta['scope']['horizon'],3)

    def test_each_mode_maps_to_its_own_lean_monitor(self):
        expected={'retryable':('checkResidenceValues','behavioralResidenceProbability'),
                  'first_entry':('checkFirstEntryValues','behavioralFirstEntryProbability'),
                  'avoid':('checkAvoidValues','behavioralAvoidResidenceProbability')}
        for mode,(checker,probability) in expected.items():
            raw=problem(mode=mode,semantics='completion_by',deadline=3)
            with self.subTest(mode=mode):
                source,meta=emit_source(raw,solve_residence(raw))
                self.assertEqual(meta['scope']['mode'],mode)
                self.assertIn(f'theorem receipt_checked : {checker} sys',source)
                self.assertIn(probability,source)
                for other,(other_checker,_) in expected.items():
                    if other!=mode:
                        self.assertNotIn(other_checker+' ',source)
                self.assertEqual('def dangerSet ' in source,mode=='avoid')
        source,_=emit_source(problem(mode='avoid',semantics='completion_by',deadline=3),
                             solve_residence(problem(mode='avoid',semantics='completion_by',deadline=3)))
        self.assertIn('theorem receipt_checked : checkAvoidValues sys targetSet dangerSet dwell latest values',source)

    def test_horizon_and_dimension_scope(self):
        raw=problem(dwell=2,deadline=MAX_HORIZON)
        with self.assertRaises(AppError) as raised:emit_source(raw,solve_residence(raw))
        self.assertEqual(raised.exception.code,'RESIDENCE_REIFY_SCOPE')
        raw=json.loads(EXAMPLE.read_text())
        with self.assertRaises(AppError) as raised:emit_source(raw,solve_residence(raw))
        self.assertEqual(raised.exception.code,'REIFICATION_SCOPE')

    def test_tampered_receipts_never_emit(self):
        raw=problem()
        receipt=solve_residence(raw)
        mutations=[]
        bad=deepcopy(receipt);bad['probability_by_initial_state'][0]='1/2';mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        bad=deepcopy(receipt);bad['mode']='first_entry';mutations.append(bad)
        mutations.append(solve_residence(problem(deadline=1)))
        for item in mutations:
            with self.subTest(item=item.get('probability_by_initial_state')),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_source_recheck_binds_original_bytes(self):
        raw=problem()
        receipt=solve_residence(raw)
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'problem.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'problem.json',base/'receipt.json',base/'out')
            result=check_family('residence',base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.ResidenceSourceRecheck.v1')
            self.assertEqual(result['status'],'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF')
            lean=base/'out/ReifiedResidence.lean'
            lean.write_text(lean.read_text().replace('def dwell : ℕ := 1','def dwell : ℕ := 2',1))
            with self.assertRaises(AppError) as raised:
                check_family('residence',base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'RESIDENCE_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
