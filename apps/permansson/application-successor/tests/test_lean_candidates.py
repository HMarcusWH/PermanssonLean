"""Unified `lean-emit` / `lean-recheck` CLI over every source-candidate family.

The per-family emitters and their byte rechecks are tested in the
family-specific test modules; these tests check the single dispatcher, its
argument arity and real CLI round trips for representative layouts. No Lean
is run.
"""
from __future__ import annotations
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

APP=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(APP/'src'))
from permansson_app.engines.exit import compute_exit,parse_region
from permansson_app.engines.lp import propose_lp_optimum
from permansson_app.engines.private_stage import propose_private_stage
from permansson_app.errors import AppError
from permansson_app.finite_world import parse_finite_world
from permansson_app.engines.lp_types import parse_lp
from permansson_app.proof import lean_candidates
from permansson_app.proof.control_source_check import FAMILIES,REGION_FAMILIES

EXAMPLES=APP/'src/permansson_app/data/examples'


def _cli(*args):
    env=os.environ.copy();env['PYTHONDONTWRITEBYTECODE']='1';env['PYTHONPATH']=str(APP/'src')
    return subprocess.run([sys.executable,'-B','-m','permansson_app',*map(str,args)],
                          cwd=APP,env=env,text=True,capture_output=True,timeout=120)


def _write(path,value):
    path.write_text(json.dumps(value));return path


class LeanCandidateDispatchTests(unittest.TestCase):
    def test_family_set_covers_every_emitter(self):
        self.assertEqual(set(lean_candidates.families()),set(FAMILIES)|{'finite-world','lp'})
        for family,(_,emitter,lean_name,code,fmt) in FAMILIES.items():
            with self.subTest(family=family):
                self.assertTrue(callable(emitter.emit_files))
                self.assertTrue(lean_name.startswith('Reified') and lean_name.endswith('.lean'))
                self.assertGreater(emitter.MAX_SOURCE_BYTES,0)

    def test_arity_is_enforced_before_any_file_is_read(self):
        missing=Path('/nonexistent/request.json')
        cases=[('no-such-family',missing,missing,None),
               ('private-stage',missing,None,None),                 # receipt required
               ('finite-world',missing,missing,None),               # receipt not accepted
               ('exit',missing,missing,None),                       # region required
               ('private-stage',missing,missing,missing)]           # region not accepted
        for family,request,receipt,region in cases:
            with self.subTest(family=family),self.assertRaises(AppError) as raised:
                lean_candidates.emit(family,request,receipt,Path('/nonexistent/out'),region)
            self.assertEqual(raised.exception.code,'REIFY_FAMILY')
        self.assertEqual(REGION_FAMILIES,{'exit'})

    def test_private_stage_cli_round_trip_and_tamper(self):
        raw=json.loads((EXAMPLES/'private_stage.v1.json').read_text())
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            request=_write(base/'request.json',raw)
            receipt=_write(base/'receipt.json',propose_private_stage(raw))
            p=_cli('lean-emit','--family','private-stage',request,receipt,'--output',base/'out')
            self.assertEqual(p.returncode,0,p.stderr)
            emitted=json.loads(p.stdout)
            self.assertEqual((emitted['family'],emitted['result']['lean_status']),('private-stage','NOT_EXECUTED'))
            p=_cli('lean-recheck','--family','private-stage',request,receipt,'--candidate',base/'out')
            self.assertEqual(p.returncode,0,p.stderr)
            checked=json.loads(p.stdout)['result']
            self.assertEqual(checked['status'],'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF')
            self.assertIs(checked['independent_math_certification'],False)
            self.assertEqual(checked['lean_source_sha256'],emitted['result']['candidate_sha256'])
            lean=base/'out/ReifiedPrivateStage.lean'
            lean.write_text(lean.read_text().replace('theorem solver_value','theorem solver_value_hidden',1))
            p=_cli('lean-recheck','--family','private-stage',request,receipt,'--candidate',base/'out')
            self.assertEqual(p.returncode,2)
            self.assertEqual(json.loads(p.stderr)['error']['code'],'PRIVATE_STAGE_REIFY_SOURCE')
            # The emitter never overwrites an existing candidate.
            p=_cli('lean-emit','--family','private-stage',request,receipt,'--output',base/'out')
            self.assertEqual(p.returncode,2)

    def test_finite_world_lp_and_region_layouts(self):
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            model=EXAMPLES/'finite_world.v1.model.json'
            self.assertEqual(lean_candidates.emit('finite-world',model,None,base/'fw')['lean_status'],'NOT_EXECUTED')
            self.assertEqual(lean_candidates.recheck('finite-world',model,None,base/'fw')['lean_status'],'NOT_EXECUTED')

            raw=json.loads((EXAMPLES/'lp.v1.model.json').read_text())
            lp_request=_write(base/'lp.json',raw)
            lp_receipt=_write(base/'lp_receipt.json',propose_lp_optimum(parse_lp(raw))['receipt'])
            lean_candidates.emit('lp',lp_request,lp_receipt,base/'lp')
            self.assertEqual(lean_candidates.recheck('lp',lp_request,lp_receipt,base/'lp')['lean_status'],'NOT_EXECUTED')

            fixtures=APP/'tests/fixtures'
            raw=json.loads((fixtures/'occupation_transient_split.v1.json').read_text())
            region=json.loads((fixtures/'occupation_transient_split.region_closed_class.v1.json').read_text())
            world=parse_finite_world(raw)
            exit_model=_write(base/'model.json',raw);exit_region=_write(base/'region.json',region)
            exit_receipt=_write(base/'exit_receipt.json',compute_exit(world,parse_region(region,world)))
            p=_cli('lean-emit','--family','exit',exit_model,exit_receipt,'--region',exit_region,'--output',base/'exit')
            self.assertEqual(p.returncode,0,p.stderr)
            p=_cli('lean-recheck','--family','exit',exit_model,exit_receipt,'--region',exit_region,'--candidate',base/'exit')
            self.assertEqual(p.returncode,0,p.stderr)
            self.assertEqual(json.loads(p.stdout)['result']['format'],'Permansson.App.ExitSourceRecheck.v1')


if __name__=='__main__':
    unittest.main()
