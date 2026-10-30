"""Source-bound frozen-menu Lean candidates: binding and status boundaries.

Compiler replay is exercised by verification/research/
test_application_menu_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.menu import propose_menu
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.menu_emit import FORMAT,MAX_HORIZON,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/finite_menu.v1.json'


def fixture():
    raw=json.loads(EXAMPLE.read_text())
    return raw,propose_menu(raw)


class MenuEmitTests(unittest.TestCase):
    def test_checked_menu_emits_held_fixed_and_listed_optimality(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['member_ids'],['untreated','treated'])
        self.assertEqual(meta['scope']['optimality'],'DECLARED_MENU_ONLY')
        self.assertIn('def members : Fin 2 → RationalMarkovMatrix (2 * 2) := fun i => '
                      '(if i = (0 : Fin 2) then inducedMatrix member_0 else inducedMatrix member_1)',source)
        self.assertIn('theorem receipt_checked :',source)
        self.assertIn('def tied : Finset (Fin 2) := ({0} : Finset (Fin 2))',source)
        self.assertIn('def survival : Bool := true',source)
        self.assertIn('def maximize : Bool := false',source)
        # Both members declare alpha interventions, so U must be held fixed.
        for i in (0,1):
            self.assertIn(f'theorem member_{i}_held_fixed : HeldFixed base member_{i}',source)
            self.assertIn(f'theorem member_{i}_update_held_fixed :',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_exit_objective_and_max_direction(self):
        raw,_=fixture()
        raw=dict(raw,value_type='exit_by_horizon',direction='max')
        source,meta=emit_source(raw,propose_menu(raw))
        self.assertIn('def survival : Bool := false',source)
        self.assertIn('def maximize : Bool := true',source)
        self.assertNotIn('1 - hittingValue',source)

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['menu_values'][0]['value']='1/3';mutations.append(bad)
        bad=deepcopy(receipt);bad['attaining_ids']=['treated'];bad['representative_id']='treated';mutations.append(bad)
        bad=deepcopy(receipt);bad['attaining_ids']=['treated','untreated'];mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['attaining_ids']),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_scope_limits(self):
        raw,_=fixture()
        raw=dict(raw,horizon=MAX_HORIZON+1)
        with self.assertRaises(AppError) as raised:emit_source(raw,propose_menu(raw))
        self.assertEqual(raised.exception.code,'MENU_REIFY_SCOPE')

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('menu',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.MenuSourceRecheck.v1')
            self.assertEqual(result['status'],'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF')
            lean=base/'out/ReifiedMenu.lean'
            lean.write_text(lean.read_text().replace('def maximize : Bool := false','def maximize : Bool := true',1))
            with self.assertRaises(AppError) as raised:
                check_family('menu',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'MENU_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
