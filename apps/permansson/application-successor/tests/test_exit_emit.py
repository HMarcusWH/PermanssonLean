"""Source-bound first-exit routing Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_exit_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.exit import compute_exit,parse_region
from permansson_app.errors import AppError
from permansson_app.finite_world import parse_finite_world
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.exit_emit import FORMAT,MAX_HORIZON,emit_files,emit_source,stopped_certificate
from permansson_app.finite_world import induced_kernel

MODEL=APP/'tests/fixtures/occupation_transient_split.v1.json'
CLOSED=APP/'tests/fixtures/occupation_transient_split.region_closed_class.v1.json'


def fixture(region_path=CLOSED):
    raw=json.loads(MODEL.read_text());region=json.loads(region_path.read_text())
    model=parse_finite_world(raw)
    return raw,region,compute_exit(model,parse_region(region,model))


class ExitEmitTests(unittest.TestCase):
    def test_checked_receipt_emits_routing_and_never_exit(self):
        raw,region,receipt=fixture()
        source,meta=emit_source(raw,region,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['region'],[0,1,2])
        self.assertEqual(meta['scope']['outside'],[3])
        self.assertEqual(meta['scope']['stopped_chain_classes'],[[1,2],[3]])
        self.assertEqual(meta['scope']['interpretation'],'SUBPROBABILITY_ROUTING_PLUS_NEVER_EXIT_MASS')
        names=meta['theorem_names']
        self.assertEqual(names[0],'receipt_checked')
        for name in ('survival_0','never_exit_0','exit_within_horizon_0_3','eventual_exit_0_3'):
            self.assertIn(name,names)
        self.assertIn('checkExitRoutingReceipt K region horizon survival steps cert eventual never = true',source)
        block=source.split('theorem never_exit_0 :',1)[1].split('theorem ',1)[0]
        self.assertIn('((((1 : ℚ) / (2 : ℚ)) : ℚ) : ℝ)',block)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_stopped_certificate_keeps_inside_class_and_absorbs_outside(self):
        raw,_,_=fixture()
        classes,weights=stopped_certificate(induced_kernel(parse_finite_world(raw)),[0,1,2])
        self.assertEqual(classes,[[1,2],[3]])
        self.assertEqual([str(v) for v in weights[1]],['1/2','0','0','1'])

    def test_tampered_receipts_never_emit(self):
        raw,region,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['rows'][0]['eventual_exit_by_destination']=['1'];bad['rows'][0]['never_exit']='0';mutations.append(bad)
        bad=deepcopy(receipt);bad['rows'][0]['survival_through'][1]='1/3';mutations.append(bad)
        bad=deepcopy(receipt);bad['rows'][0]['first_exit_by_step_and_destination'][0]=['1/2'];mutations.append(bad)
        bad=deepcopy(receipt);bad['outside_indices']=[2];mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['outside_indices']),self.assertRaises(AppError):
                emit_source(raw,region,item)

    def test_scope_limit(self):
        raw,region,_=fixture()
        region=dict(region,horizon=MAX_HORIZON+1)
        model=parse_finite_world(raw)
        receipt=compute_exit(model,parse_region(region,model))
        with self.assertRaises(AppError) as raised:emit_source(raw,region,receipt)
        self.assertEqual(raised.exception.code,'EXIT_REIFY_SCOPE')

    def test_source_recheck_binds_model_region_and_receipt_bytes(self):
        raw,region,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'model.json').write_text(json.dumps(raw))
            (base/'region.json').write_text(json.dumps(region))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'model.json',base/'region.json',base/'receipt.json',base/'out')
            result=check_family('exit',base/'model.json',base/'receipt.json',base/'out',base/'region.json')
            self.assertEqual(result['format'],'Permansson.App.ExitSourceRecheck.v1')
            with self.assertRaises(AppError) as raised:
                check_family('exit',base/'model.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'REIFY_FAMILY')
            (base/'region.json').write_text(json.dumps(region,indent=1))
            with self.assertRaises(AppError) as raised:
                check_family('exit',base/'model.json',base/'receipt.json',base/'out',base/'region.json')
            self.assertEqual(raised.exception.code,'EXIT_REIFY_RECEIPT')


if __name__=='__main__':
    unittest.main()
