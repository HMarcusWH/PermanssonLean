"""Source-bound almost-sure safety-core Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_safety_core_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.safety import parse_safety_problem,propose_safety_core
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.safety_emit import FORMAT,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/finite_safety.v1.json'


def small_problem()->dict:
    """2x2 joint space; state 2 leaks under every action, state 1 must move
    to 2, state 0 can stay: core {0} after two pruning steps."""
    S,X=['s0','s1'],['x0','x1']
    feasible={('s0','x0'):['stay','risky'],('s0','x1'):['risky'],
              ('s1','x0'):['stay','risky'],('s1','x1'):['stay']}
    alpha={('s0','x0'):{'stay':'1/2','risky':'1/2'},('s0','x1'):{'stay':'0','risky':'1'},
           ('s1','x0'):{'stay':'1','risky':'0'},('s1','x1'):{'stay':'1','risky':'0'}}
    P={('s0','x0','stay'):{'x0':'1','x1':'0'},('s0','x0','risky'):{'x0':'1/2','x1':'1/2'},
       ('s0','x1','risky'):{'x0':'1','x1':'0'},('s1','x0','stay'):{'x0':'0','x1':'1'},
       ('s1','x0','risky'):{'x0':'1/2','x1':'1/2'},('s1','x1','stay'):{'x0':'0','x1':'1'}}
    def U(s,x,a):
        if (s,x,a)==('s0','x0','risky'):return {'s0':'1/2','s1':'1/2'}
        if (s,x,a)==('s0','x1','risky'):return {'s0':'0','s1':'1'}
        return {s:'1',('s1' if s=='s0' else 's0'):'0'}
    model={'format':'Permansson.App.FiniteStrategicWorld.v1',
           'states':{'strategic':S,'world':X,'actions':['stay','risky']},
           'feasible':[{'s':s,'x':x,'actions':feasible[s,x]} for s in S for x in X],
           'alpha':[{'s':s,'x':x,'weights':alpha[s,x]} for s in S for x in X],
           'P':[{'s':s,'x':x,'a':a,'weights':P[s,x,a]} for s in S for x in X for a in feasible[s,x]],
           'U':[{'s':s,'x':x,'a':a,'xp':xp,'weights':U(s,x,a)}
                for s in S for x in X for a in feasible[s,x] for xp in X]}
    return {'format':'Permansson.App.FiniteSafetyCore.v1','model':model,
            'safe':[{'strategic':'s0','world':'x0'},{'strategic':'s0','world':'x1'},
                    {'strategic':'s1','world':'x0'}]}


def fixture():
    raw=small_problem()
    problem=parse_safety_problem(raw)
    return raw,problem,propose_safety_core(problem)


class SafetyEmitTests(unittest.TestCase):
    def test_checked_core_emits_infinite_horizon_theorems_without_status_promotion(self):
        _,problem,receipt=fixture()
        source,meta=emit_source(problem,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertIn('boundControlSystem input options options_exact states_pos',source)
        self.assertIn('theorem receipt_checked : checkInvariantCore sys safeRegion core witness = true',source)
        self.assertIn('checked_outside_core_not_almost_sure',source)
        self.assertEqual(meta['scope']['core'],[0])
        self.assertEqual(meta['scope']['excluded_from_core'],[1,2])
        self.assertEqual(meta['theorem_names'],['options_exact','receipt_checked','core_greatest_invariant',
            'core_iff_almost_sure','core_iff_value_one','almost_sure_safe_0',
            'not_almost_sure_1','not_almost_sure_2'])
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))
        self.assertIsNone(re.search(r'(?m)^\s*((private|protected|noncomputable|unsafe)\s+)*axiom\s',source))

    def test_witness_reflects_receipt_on_core_and_fill_elsewhere(self):
        _,problem,receipt=fixture()
        source,meta=emit_source(problem,receipt)
        witness=next(l for l in source.splitlines() if l.startswith('def witness '))
        # core state 0 uses the receipt's `stay` (index 0); state 1 has only
        # `risky` (index 1) feasible, which is its first declared action.
        self.assertIn('(if y = (0 : Fin 4) then (0 : Fin 2) else (if y = (1 : Fin 4) then (1 : Fin 2)',witness)
        self.assertEqual(meta['noncore_witness_fill'],'first_declared_feasible_action')

    def test_tampered_receipts_never_emit(self):
        _,problem,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['core_indices']=[0,1];mutations.append(bad)
        bad=deepcopy(receipt);bad['stationary_witness_actions']=[{'state_index':0,'action':'risky'}];mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        bad=deepcopy(receipt);bad['descending_pruning_chain']=[[0,1,2],[0]];mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item),self.assertRaises(AppError):
                emit_source(problem,item)

    def test_packaged_three_world_example_stays_numeric_only(self):
        problem=parse_safety_problem(json.loads(EXAMPLE.read_text()))
        with self.assertRaises(AppError) as raised:
            emit_source(problem,propose_safety_core(problem))
        self.assertEqual(raised.exception.code,'REIFICATION_SCOPE')

    def test_source_recheck_binds_original_bytes(self):
        raw,problem,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'problem.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'problem.json',base/'receipt.json',base/'out')
            result=check_family('safety-core',base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(result['status'],'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF')
            self.assertEqual(result['format'],'Permansson.App.SafetyCoreSourceRecheck.v1')
            with self.assertRaises(AppError) as raised:
                check_family('control-table',base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'CONTROL_REIFY_PATH')
            lean=base/'out/ReifiedSafetyCore.lean'
            lean.write_text(lean.read_text().replace('({0} : Finset (Fin 4))','({0, 1} : Finset (Fin 4))',1))
            with self.assertRaises(AppError) as raised:
                check_family('safety-core',base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'SAFETY_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
