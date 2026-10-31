"""Source-bound observe-then-act belief Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_belief_live_lean.py; these tests need no Lean.
"""
from __future__ import annotations
from copy import deepcopy
import json
from pathlib import Path
import re
import sys
import tempfile
import unittest
from unittest import mock

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.engines.belief import propose_belief
from permansson_app.engines.belief_tree import propose_belief_tree
from permansson_app.errors import AppError
from permansson_app.proof import belief_emit
from permansson_app.proof.belief_emit import FORMAT,emit_files,emit_source
from permansson_app.proof.control_source_check import check_family

EXAMPLES=APP/'src/permansson_app/data/examples'
RESTRICTED=APP/'tests/fixtures/belief_tree_restricted.v1.json'
DEAD_END=APP/'tests/fixtures/belief_tree_dead_end.v1.json'


def one_step():
    raw=json.loads((EXAMPLES/'belief.v1.json').read_text())
    return raw,propose_belief(raw)


def tree(path=EXAMPLES/'belief_tree.v1.json',**changes):
    raw=dict(json.loads(path.read_text()),**changes)
    return raw,propose_belief_tree(raw)


class BeliefEmitTests(unittest.TestCase):
    def test_one_step_is_the_horizon_one_tree(self):
        raw,receipt=one_step()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['profile'],'ONE_STEP')
        self.assertEqual(meta['scope']['horizon'],1)
        self.assertEqual(meta['theorem_names'],['options_exact','likelihood_nonneg','likelihood_sum_one',
            'prior_nonneg','prior_sum_one','receipt_checked','observation_optimum',
            'terminal_law_0','terminal_law_1','blind_checked','blind_baseline','value_of_observation'])
        # green -> leave, red -> repair, unreachable unseen -> filled with action 0
        self.assertIn('def roots : Fin 3 → Belief.Tree (Fin 2) (Fin 3) 1 := fun o0 => '
                      '(if o0 = (0 : Fin 3) then ((0 : Fin 2), fun _ => PUnit.unit) else '
                      '(if o0 = (1 : Fin 3) then ((1 : Fin 2), fun _ => PUnit.unit) else '
                      '((0 : Fin 2), fun _ => PUnit.unit)))',source)
        self.assertIn('def D : ℚ := ((13 : ℚ) / (16 : ℚ))',source)
        self.assertIn('def blindSeq : List (Fin 2) := [(1 : Fin 2)]',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_tree_reflects_joint_states_and_admitted_actions(self):
        raw,receipt=tree(RESTRICTED)
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['scope']['profile'],'TREE')
        self.assertEqual((meta['scope']['ns'],meta['scope']['nx'],meta['scope']['horizon']),(2,2,3))
        self.assertIn('def options : Fin (2 * 2) → Finset (Fin 2) := fun y => (if y = (0 : Fin 4) then '
                      '({0, 1} : Finset (Fin 2)) else (if y = (1 : Fin 4) then ({1} : Finset (Fin 2))',source)
        self.assertIn('def D : ℚ := ((121 : ℚ) / (512 : ℚ))',source)
        self.assertIn('def blindSeq : List (Fin 2) := [(1 : Fin 2), (1 : Fin 2), (1 : Fin 2)]',source)
        self.assertEqual(len([n for n in meta['theorem_names'] if n.startswith('terminal_law_')]),4)

    def test_blind_baseline_outside_the_lean_recursion_is_refused(self):
        # Lean values an empty admitted set at 0; such a maximum, or one that
        # differs from the receipt, is refused rather than emitted.
        raw,receipt=tree(RESTRICTED)
        original=belief_emit._blind_mirror
        for patched in (lambda *a:original(*a)[:2]+(False,),
                        lambda *a:(original(*a)[0]+1,)+original(*a)[1:]):
            with self.subTest(),mock.patch.object(belief_emit,'_blind_mirror',patched):
                with self.assertRaises(AppError) as raised:
                    emit_source(raw,receipt)
                self.assertEqual(raised.exception.code,'BELIEF_REIFY_SCOPE')

    def test_tampered_receipts_never_emit(self):
        raw,receipt=tree()
        mutations=[]
        bad=deepcopy(receipt);bad['optimal_expected_terminal_reward']='1';mutations.append(bad)
        bad=deepcopy(receipt);bad['optimal_policy_tree']['observations'][0]['selected_action']='repair'
        mutations.append(bad)
        bad=deepcopy(receipt);bad['terminal_joint_law']=['9/64','55/64'];mutations.append(bad)
        bad=deepcopy(receipt);bad['best_blind_action_sequence_reward']='55/64';mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['optimal_expected_terminal_reward']),self.assertRaises(AppError):
                emit_source(raw,item)
        raw,receipt=one_step()
        bad=deepcopy(receipt);bad['policy'][1]['selected_action']='leave'
        with self.assertRaises(AppError):
            emit_source(raw,bad)

    def test_unsupported_request_never_emits(self):
        raw,receipt=tree()
        with self.assertRaises(AppError) as raised:
            emit_source(dict(raw,format='Permansson.App.Unknown.v1'),receipt)
        self.assertEqual(raised.exception.code,'BELIEF_REIFY_INPUT')

    def test_equal_observed_and_blind_values_use_a_calc_chain(self):
        # Observation does not help here (D = B = 2).  A rewrite of the checked
        # inequality would let rw's closing rfl discharge the goal first, so the
        # emitted proof is a calc chain through the checked definitions.
        raw,receipt=tree(DEAD_END)
        source,_=emit_source(raw,receipt)
        self.assertIn('def D : ℚ := (2 : ℚ)',source)
        self.assertIn('def B : ℚ := (2 : ℚ)',source)
        self.assertIn('  calc ((2 : ℚ) : ℚ) = B := hB.symm\n    _ ≤ D := h\n    _ = (2 : ℚ) := hD\n',source)
        self.assertNotIn('rw [hD, hB] at h',source)

    def test_source_recheck_binds_original_bytes(self):
        for raw,receipt,family_name in (one_step()+('one',),tree()+('tree',)):
            with self.subTest(case=family_name),tempfile.TemporaryDirectory() as td:
                base=Path(td)
                (base/'request.json').write_text(json.dumps(raw))
                (base/'receipt.json').write_text(json.dumps(receipt))
                emit_files(base/'request.json',base/'receipt.json',base/'out')
                result=check_family('belief',base/'request.json',base/'receipt.json',base/'out')
                self.assertEqual(result['format'],'Permansson.App.BeliefSourceRecheck.v1')
                lean=base/'out/ReifiedBelief.lean'
                text=lean.read_text()
                changed=re.sub(r'def D : ℚ := [^\n]*','def D : ℚ := (1 : ℚ)',text,count=1)
                self.assertNotEqual(changed,text)
                lean.write_text(changed)
                with self.assertRaises(AppError) as raised:
                    check_family('belief',base/'request.json',base/'receipt.json',base/'out')
                self.assertEqual(raised.exception.code,'BELIEF_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
