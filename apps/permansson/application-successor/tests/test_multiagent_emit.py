"""Source-bound two-player protocol Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_multiagent_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.multiagent import propose_multiagent
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.multiagent_emit import FORMAT,emit_files,emit_source

EXAMPLE=APP/'src/permansson_app/data/examples/multiagent.v1.json'


def fixture():
    raw=json.loads(EXAMPLE.read_text())
    return raw,propose_multiagent(raw)


class MultiAgentEmitTests(unittest.TestCase):
    def test_protocol_emits_bound_instance(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['theorem_names'],['receipt_checked','hps','hc','hr','ha',
                                                'protocol_kernels','marked_path_transport'])
        self.assertIn('def i : Fin 2 := 0',source)
        self.assertIn('def ps : Fin 2 → Player 1 2 2 2 := fun j => if j = 0 then p0 else p1',source)
        self.assertIn('  ⟨fun y a x _s =>',source)  # one common state: its coordinate is unused
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        for key,value in (('closed_open_max_tv','0'),('lean_status','PASS'),('treated_player',1)):
            bad=deepcopy(receipt);bad[key]=value
            with self.subTest(key=key),self.assertRaises(AppError):
                emit_source(raw,bad)

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'request.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'request.json',base/'receipt.json',base/'out')
            result=check_family('multiagent',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.MultiAgentSourceRecheck.v1')
            lean=base/'out/ReifiedMultiAgent.lean'
            text=lean.read_text()
            changed=text.replace('def i : Fin 2 := 0','def i : Fin 2 := 1',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('multiagent',base/'request.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'MULTIAGENT_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
