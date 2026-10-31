"""Source-bound finite-horizon perturbation Lean candidates: binding and boundaries.

Compiler replay is exercised by verification/research/
test_application_perturbation_live_lean.py; these tests need no Lean.
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
from permansson_app.engines.robustness import parse_perturbation,propose_perturbation
from permansson_app.errors import AppError
from permansson_app.proof.control_source_check import check_family
from permansson_app.proof.perturbation_emit import FORMAT,MAX_HORIZON,emit_files,emit_source

FIXTURE=APP/'tests/fixtures/perturbation_transient_split.v1.json'
PACKAGED=APP/'src/permansson_app/data/examples/finite_perturbation.v1.json'


def fixture(path=FIXTURE):
    raw=json.loads(path.read_text())
    return raw,propose_perturbation(parse_perturbation(raw))


class PerturbationEmitTests(unittest.TestCase):
    def test_checked_receipt_emits_budget_and_event_theorems(self):
        raw,receipt=fixture()
        source,meta=emit_source(raw,receipt)
        self.assertEqual(meta['format'],FORMAT)
        self.assertEqual(meta['scope']['interpretation'],'FINITE_HORIZON_REGION_SURVIVAL_TV_BUDGET_ONLY')
        self.assertEqual(meta['theorem_names'][:3],['receipt_checked','event_probabilities','perturbation_bound'])
        self.assertEqual(sum(n.startswith('row_event_tv_') for n in meta['theorem_names']),4)
        self.assertIn('def K : RationalMarkovMatrix (2 * 2) := inducedMatrix base',source)
        self.assertIn('def L : RationalMarkovMatrix (2 * 2) := inducedMatrix alt',source)
        self.assertIn('def bound : ℚ := ((3 : ℚ) / (4 : ℚ))',source)
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        for flag in ('compiler_evidence_authenticated','independent_math_certification',
                     'empirical_identification','application_release_authorized'):
            self.assertIs(meta[flag],False)
        self.assertIsNone(re.search(r'(^|[^A-Za-z0-9_])(sorry|admit|native_decide)([^A-Za-z0-9_]|$)',source))

    def test_packaged_three_world_example_exceeds_reflection_bound(self):
        raw,receipt=fixture(PACKAGED)
        with self.assertRaises(AppError) as raised:emit_source(raw,receipt)
        self.assertEqual(raised.exception.code,'REIFICATION_SCOPE')

    def test_tampered_receipts_never_emit(self):
        raw,receipt=fixture()
        mutations=[]
        bad=deepcopy(receipt);bad['maximum_row_tv']='1/12';mutations.append(bad)
        bad=deepcopy(receipt);bad['bound_at_horizon']='1/2';mutations.append(bad)
        bad=deepcopy(receipt);bad['initial_law_tv']='0';mutations.append(bad)
        bad=deepcopy(receipt);bad['baseline_event_probability']='1/2';mutations.append(bad)
        bad=deepcopy(receipt);bad['lean_status']='PASS';mutations.append(bad)
        for item in mutations:
            with self.subTest(item=item['bound_at_horizon']),self.assertRaises(AppError):
                emit_source(raw,item)

    def test_scope_limit(self):
        raw,_=fixture()
        raw=dict(raw,horizon=MAX_HORIZON+1)
        receipt=propose_perturbation(parse_perturbation(raw))
        with self.assertRaises(AppError) as raised:emit_source(raw,receipt)
        self.assertEqual(raised.exception.code,'PERTURBATION_REIFY_SCOPE')

    def test_source_recheck_binds_original_bytes(self):
        raw,receipt=fixture()
        with tempfile.TemporaryDirectory() as td:
            base=Path(td)
            (base/'problem.json').write_text(json.dumps(raw))
            (base/'receipt.json').write_text(json.dumps(receipt))
            emit_files(base/'problem.json',base/'receipt.json',base/'out')
            result=check_family('perturbation',base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(result['format'],'Permansson.App.PerturbationSourceRecheck.v1')
            lean=base/'out/ReifiedPerturbation.lean'
            text=lean.read_text()
            changed=text.replace('def bound : ℚ := ((3 : ℚ) / (4 : ℚ))','def bound : ℚ := ((1 : ℚ) / (2 : ℚ))',1)
            self.assertNotEqual(changed,text)
            lean.write_text(changed)
            with self.assertRaises(AppError) as raised:
                check_family('perturbation',base/'problem.json',base/'receipt.json',base/'out')
            self.assertEqual(raised.exception.code,'PERTURBATION_REIFY_SOURCE')


if __name__=='__main__':
    unittest.main()
