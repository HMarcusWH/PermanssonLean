"""Source-bound Bellman control-table Lean candidates: binding and status boundaries.

Compiler replay is exercised by verification/research/
test_application_control_table_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.hitting import parse_hitting_problem,propose_bellman
from permansson_app.errors import AppError
from permansson_app.proof.control_emit import FORMAT,MAX_HORIZON,emit_files,emit_source
from permansson_app.proof.control_source_check import check_files

EXAMPLE=APP/'src/permansson_app/data/examples/control_hitting.v1.json'


def fixture(horizon=None):
    raw=json.loads(EXAMPLE.read_text())
    if horizon is not None:raw['horizon']=horizon
    problem=parse_hitting_problem(raw)
    return raw,problem,propose_bellman(problem)


class ControlEmitTests(unittest.TestCase):
    def test_checked_receipt_emits_bound_theorems_without_status_promotion(self):
        _,problem,receipt=fixture()
        source,meta=emit_source(problem,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertIn('boundControlSystem input options options_exact states_pos',source)
        self.assertIn('checkBellmanReceipt_sound_of_finite_world',source)
        self.assertIn('theorem receipt_checked : checkBellmanReceipt sys target 3 values chosen = true',source)
        self.assertEqual(meta['theorem_names'][:6],['options_exact','receipt_checked','bellman_values',
            'schedule_upper_bound','optimum_attained','selected_feasible'])
        self.assertEqual(meta['theorem_names'][6:],['bellman_value_0','bellman_value_1'])
        self.assertEqual(meta['scope'],{'ns':1,'nx':2,'na':2,'joint_states':2,'horizon':3})
        self.assertEqual(meta['problem_semantic_identity'],problem.semantic_id)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        # Same token boundary as the Research Lean placeholder scan.
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))
        self.assertIsNone(re.search(r'(?m)^\s*((private|protected|noncomputable|unsafe)\s+)*axiom\s',source))

    def test_chosen_table_is_shifted_by_one_remaining_transition(self):
        _,problem,receipt=fixture()
        source,_=emit_source(problem,receipt)
        chosen=next(l for l in source.splitlines() if l.startswith('def chosen '))
        # Lean chosen t is applied with t+1 remaining: receipt row 1 selects
        # `move` (index 1) at x0; rows 2..3 select `stay` (index 0); the goal
        # state x1 is terminal and filled with its first feasible action.
        self.assertIn('(if t = 0 then (if y = (0 : Fin 2) then (1 : Fin 2) else (0 : Fin 2))',chosen)
        self.assertIn('(if t = 1 then (if y = (0 : Fin 2) then (0 : Fin 2) else (0 : Fin 2))',chosen)

    def test_emission_is_deterministic(self):
        _,problem,receipt=fixture()
        self.assertEqual(emit_source(problem,receipt),emit_source(problem,deepcopy(receipt)))

    def test_tampered_or_mismatched_receipts_never_emit(self):
        _,problem,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['values_by_remaining_transitions'][2][0]='1/2';mutations.append(bad)
        bad=deepcopy(receipt);bad['selected_actions_by_remaining_transitions'][1][0]='stay';mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        bad=deepcopy(receipt);bad['scientific_claims_verified']=True;mutations.append(bad)
        _,other,other_receipt=fixture(horizon=2)
        mutations.append(other_receipt)
        for item in mutations:
            with self.subTest(item=item),self.assertRaises(AppError):
                emit_source(problem,item)

    def test_scope_limits(self):
        _,problem,receipt=fixture(horizon=0)
        with self.assertRaises(AppError) as raised:emit_source(problem,receipt)
        self.assertEqual(raised.exception.code,'CONTROL_REIFY_SCOPE')
        _,problem,receipt=fixture(horizon=MAX_HORIZON+1)
        with self.assertRaises(AppError) as raised:emit_source(problem,receipt)
        self.assertEqual(raised.exception.code,'CONTROL_REIFY_SCOPE')
        # Three world states exceed the literal reflection dimension (<=2),
        # although the numeric Bellman engine itself accepts them.
        X=['x0','x1','x2']
        raw={'format':'Permansson.App.FiniteHittingControl.v1','horizon':1,'forbidden':[],
             'goal':[{'strategic':'s0','world':'x2'}],
             'model':{'format':'Permansson.App.FiniteStrategicWorld.v1',
                      'states':{'strategic':['s0'],'world':X,'actions':['stay']},
                      'feasible':[{'s':'s0','x':x,'actions':['stay']} for x in X],
                      'alpha':[{'s':'s0','x':x,'weights':{'stay':'1'}} for x in X],
                      'P':[{'s':'s0','x':x,'a':'stay','weights':{y:str(int(x==y)) for y in X}} for x in X],
                      'U':[{'s':'s0','x':x,'a':'stay','xp':xp,'weights':{'s0':'1'}} for x in X for xp in X]}}
        problem=parse_hitting_problem(raw)
        with self.assertRaises(AppError) as raised:emit_source(problem,propose_bellman(problem))
        self.assertEqual(raised.exception.code,'REIFICATION_SCOPE')

    def test_files_are_written_only_to_a_new_directory(self):
        raw,problem,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'problem.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            result=emit_files(base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(result['lean_status'],'NOT_EXECUTED')
            meta=json.loads((base/'out/source_candidate.json').read_text())
            self.assertEqual(meta['lean_source_sha256'],result['candidate_sha256'])
            self.assertIn('problem_bytes_sha256',meta)
            with self.assertRaises(AppError):
                emit_files(base/'problem.json',base/'receipt.json',base/'out')

    def test_source_recheck_binds_original_bytes(self):
        raw,problem,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'problem.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'problem.json',base/'receipt.json',base/'out')
            result=check_files(base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(result['status'],'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF')
            self.assertEqual(result['lean_status'],'NOT_EXECUTED')
            lean=base/'out/ReifiedControlTable.lean'
            lean.write_text(lean.read_text().replace('decide +kernel','rfl',1))
            with self.assertRaises(AppError) as raised:
                check_files(base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'CONTROL_REIFY_SOURCE')
            (base/'out/extra.lean').write_text('')
            with self.assertRaises(AppError) as raised:
                check_files(base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'CONTROL_REIFY_PATH')
            # A different but valid problem cannot re-bind the same candidate.
            (base/'out/extra.lean').unlink()
            emit_files(base/'problem.json',base/'receipt.json',base/'fresh')
            other=dict(raw,horizon=2)
            (base/'problem.json').write_text(json.dumps(other))
            with self.assertRaises(AppError):
                check_files(base/'problem.json',base/'receipt.json',base/'fresh')


if __name__=='__main__':
    unittest.main()
