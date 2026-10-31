"""Real pinned-Lean replay of checked LP optimum and Farkas instances.

This suite is picked up by the *existing* Research Lean workflow after its
library build; no mock compiler or candidate-owned success flag can pass it.
A pass proves bounded instance theorem elaboration, not independent CERT,
provenance of external experiments or release approval.
"""
from __future__ import annotations
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile
import unittest

ROOT=Path(__file__).resolve().parents[2]
APP=ROOT/'apps/permansson/application-successor'
sys.path.insert(0,str(APP/'src'))
from permansson_app.engines.lp_types import parse_lp
from permansson_app.engines.lp import propose_lp_optimum
from permansson_app.proof.lp_emit import emit_source
from permansson_app.receipts.lp import INFEASIBLE
from final_closure_case_receipts import EvidenceError, parse_target_axioms
from hashlib import sha256

AXIOM_HEADER=re.compile(
    r"(?m)^'(?P<name>[A-Za-z0-9_'.]+)' "
    r"(?:depends on axioms:|does not depend on any axioms)"
)


def _audited_axioms(log:str, expected:list[str])->dict[str,list[str]]:
    """Parse complete, target-qualified Lean records, including wrapped lists.

    Share the already-reviewed research receipt parser; malformed, foreign,
    duplicate, missing or unauthorized records cannot become PASS.
    """
    if 'error:' in log.lower() or 'sorryax' in log.lower():
        raise AssertionError('compiler/axiom diagnostic is not a clean proof')
    observed=[m.group('name') for m in AXIOM_HEADER.finditer(log)]
    if sorted(observed)!=sorted(expected) or len(observed)!=len(expected):
        raise AssertionError('unexpected/missing/duplicate theorem axiom record: '+repr(observed))
    parsed={}
    for name in expected:
        try:
            axioms=parse_target_axioms(log,name)
        except EvidenceError as exc:
            raise AssertionError('untrusted Lean axiom record: '+name) from exc
        if len(axioms)!=len(set(axioms)) or not set(axioms)<=ALLOWED:
            raise AssertionError('untrusted Lean transitive axioms for '+name)
        parsed[name]=axioms
    return parsed

ALLOWED={'propext','Classical.choice','Quot.sound'}


def _optimal():
    raw=json.loads((APP/'src/permansson_app/data/examples/lp.v1.model.json').read_text())
    lp=parse_lp(raw)
    result=propose_lp_optimum(lp)
    if result['status']!='CHECKED_OPTIMAL_CANDIDATE':
        raise AssertionError('actual optimality certificate unavailable')
    return emit_source(lp,result['receipt'])


def _farkas():
    raw=json.loads((APP/'src/permansson_app/data/examples/lp.v1.model.json').read_text())
    raw['constraints']=[{'id':'contradiction','coefficients':{'x':'1','y':'0'},
                         'relation':'<=','rhs':'-1'}]
    lp=parse_lp(raw)
    receipt={'format':INFEASIBLE,'model_semantic_identity':lp.semantic_id(),
             'multiplier':['1']}
    return emit_source(lp,receipt)


def _compile(code:str,*,timeout:int=450):
    if shutil.which('lake') is None or not (ROOT/'.lake').is_dir():
        raise AssertionError('Pinned Research Lean builder is required; no stub/skip')
    with tempfile.TemporaryDirectory(dir=ROOT/'.lake',prefix='app-lp-proof-') as td:
        path=Path(td)/'ReifiedLP.lean'
        path.write_text(code,encoding='utf-8')
        # Imported at call time: application_bridge_replay imports this module.
        from application_bridge_replay import run_bounded
        returncode,out=run_bounded(['lake','env','lean',str(path)],ROOT,timeout)
    if len(out)>250_000:
        raise AssertionError('unbounded compiler diagnostic output')
    return returncode,out


class AxiomRecordParserTests(unittest.TestCase):
    NAME='PermanssonResearch.ApplicationBridge.ReifiedLP.primal_checked'

    def test_multiline_and_empty_axiom_sets(self):
        multi=f"'{self.NAME}' depends on axioms: [propext,\n  Classical.choice,\n  Quot.sound]"
        self.assertEqual(set(_audited_axioms(multi,[self.NAME])[self.NAME]),ALLOWED)
        empty=f"'{self.NAME}' does not depend on any axioms"
        self.assertEqual(_audited_axioms(empty,[self.NAME])[self.NAME],[])

    def test_missing_foreign_duplicate_and_unterminated_records_fail_closed(self):
        good=f"'{self.NAME}' depends on axioms: [propext]"
        foreign="'PermanssonResearch.ApplicationBridge.ReifiedLP.other' depends on axioms: [propext]"
        for bad in (foreign,good+'\n'+good,good+'\n'+foreign,
                    f"'{self.NAME}' depends on axioms: [propext"):
            with self.subTest(bad=bad),self.assertRaises(AssertionError):
                _audited_axioms(bad,[self.NAME])

    def test_unknown_duplicate_and_sorry_axioms_rejected(self):
        for contents in ('sorryAx','unreviewed','propext, propext'):
            log=f"'{self.NAME}' depends on axioms: [{contents}]"
            with self.subTest(contents=contents),self.assertRaises(AssertionError):
                _audited_axioms(log,[self.NAME])


class GenuineLPBridgeTests(unittest.TestCase):
    def _positive(self,generated):
        code,meta=generated
        self.assertFalse(meta['compiler_evidence_authenticated'])
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        exitcode,log=_compile(code)
        self.assertEqual(exitcode,0,log[-9000:])
        _audited_axioms(log,meta['theorem_qualified_names'])
        return code,meta

    def _negative(self,generated,changed,expected_failed_theorems):
        # A changed objective cannot be called a discriminating mutation if
        # its ORIGINAL theorem did not compile on the same pinned compiler.
        original,meta=self._positive(generated)
        self.assertNotEqual(sha256(original.encode('utf-8')).digest(),
                            sha256(changed.encode('utf-8')).digest())
        lhs=original.splitlines();rhs=changed.splitlines()
        self.assertEqual(len(lhs),len(rhs))
        self.assertEqual(sum(a!=b for a,b in zip(lhs,rhs)),1,
                         'mutation must change exactly one source line')
        exitcode,log=_compile(changed)
        self.assertNotEqual(exitcode,0,'false rational certificate was accepted')
        lower=log.lower()
        for forbidden in ('unknown module','unknown identifier','failed to import',
                          'unexpected token','syntax error','out of memory',
                          'maximum number of heartbeats','failed to synthesize',
                          'timed out','timeout'):
            self.assertNotIn(forbidden,lower,'unrelated compiler failure: '+forbidden)
        errors=[int(m.group(1)) for m in re.finditer(
            r'ReifiedLP\.lean:(\d+):\d+: error:',log)]
        self.assertTrue(errors,'no source-anchored Lean error in rejected mutant:\n'+log[-3000:])
        # The rejection must originate at the false proof obligation,
        # not in a different import, definition or later theorem.
        theorem_lines={name:next(i for i,line in enumerate(rhs,1)
             if line.startswith('theorem '+name+' ')) for name in expected_failed_theorems}
        self.assertTrue(any(start <= err <= start+7 for start in theorem_lines.values()
                            for err in errors),
                        'no error at the falsified certificate theorem:\n'+log[-3000:])

    def test_actual_optimum_witness_and_axioms(self):
        self._positive(_optimal())

    def test_actual_farkas_infeasibility_witness_and_axioms(self):
        self._positive(_farkas())

    def test_mutated_objective_breaks_genuine_optimum_proof(self):
        generated=_optimal()
        code,_=generated
        line=next(l for l in code.splitlines() if l.startswith('def c :'))
        self.assertIn('(1 : ℚ)',line)
        changed=code.replace(line,'def c : Fin 2 → ℚ := fun j => (2 : ℚ)',1)
        self._negative(generated,changed,{'dual_checked','gap_checked'})

    def test_mutated_farkas_bound_breaks_genuine_infeasibility_proof(self):
        generated=_farkas()
        code,_=generated
        line=next(l for l in code.splitlines() if l.startswith('def b :'))
        changed=code.replace(line,'def b : Fin 1 → ℚ := fun i => (1 : ℚ)',1)
        self._negative(generated,changed,{'multiplier_bound_negative'})


if __name__=='__main__':unittest.main()
