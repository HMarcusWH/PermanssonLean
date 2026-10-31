"""Source-bound admitted patch-grammar Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_grammar_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.grammar import propose_grammar
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.grammar_emit import FORMAT,MAX_HORIZON,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/grammar.v1.json'


def fixture(**changes):
    raw=dict(json.loads(EXAMPLE.read_text()),**changes)
    return raw,propose_grammar(raw)


class GrammarEmitTests(unittest.TestCase):
    def test_checked_receipt_emits_blocks_minimality_and_corners(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['blocks'],[[],['a'],['u'],['a','u']])
        self.assertEqual(meta['scope']['admission'],'EXACT_DECLARED_BLOCKS_ONLY_NO_DOWNWARD_CLOSURE')
        names=meta['theorem_names']
        for name in ('block_1_alpha_rows','block_2_update_rows','block_3_held_fixed','receipt_checked',
                     'minimal_positive_blocks','block_value_3_0','four_corner_0_0'):
            self.assertIn(name,names)
        self.assertIn('def minimal : Finset (Fin 4) := ({1, 2} : Finset (Fin 4))',source)
        block=source.split('theorem four_corner_0_0 :',1)[1].split('theorem ',1)[0]
        self.assertIn('(((-1 : ℚ) : ℚ) : ℝ)',block)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['minimal_positive_blocks']=[['a'],['u'],['a','u']];mutations.append(bad)
        bad=deepcopy(receipt);bad['block_results'][1]['values_by_comparison_state']=['0'];mutations.append(bad)
        bad=deepcopy(receipt);bad['four_corners'][0]['interactions_by_comparison_state']=['0'];mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['minimal_positive_blocks']),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_scope_limit(self):
        raw,receipt=fixture(horizon=MAX_HORIZON+1)
        with self.assertRaises(AppError) as raised:emit_source(raw,receipt)
        self.assertEqual(raised.exception.code,'GRAMMAR_REIFY_SCOPE')

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('grammar',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.GrammarSourceRecheck.v1')
            lean=base/'out/ReifiedGrammar.lean'
            text=lean.read_text()
            changed=text.replace('def minimal : Finset (Fin 4) := ({1, 2} : Finset (Fin 4))',
                                 'def minimal : Finset (Fin 4) := ({1, 2, 3} : Finset (Fin 4))',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('grammar',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'GRAMMAR_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
