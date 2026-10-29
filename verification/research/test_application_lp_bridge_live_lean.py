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
import subprocess
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
        p=subprocess.run(['lake','env','lean',str(path)],cwd=ROOT,
                         capture_output=True,text=True,timeout=timeout)
    out=p.stdout+'\n'+p.stderr
    if len(out)>250_000:
        raise AssertionError('unbounded compiler diagnostic output')
    return p.returncode,out


class GenuineLPBridgeTests(unittest.TestCase):
    def _positive(self,generated):
        code,meta=generated
        self.assertFalse(meta['compiler_evidence_authenticated'])
        self.assertEqual(meta['lean_status'],'NOT_EXECUTED')
        exitcode,log=_compile(code)
        self.assertEqual(exitcode,0,log[-9000:])
        self.assertNotIn('error:',log.lower())
        self.assertNotIn('sorryAx',log)
        for name in meta['theorem_qualified_names']:
            # A constructive theorem may depend on *no* axioms: Lean prints
            # that using a different sentence from the nonempty-list form.
            reports=[line for line in log.splitlines() if name in line and
                     ('does not depend on any axioms' in line or
                      'depends on axioms:' in line)]
            self.assertTrue(reports,'missing transitive axiom report for '+name+'\n'+log[-4000:])
            for line in reports:
                if 'does not depend on any axioms' in line:continue
                rows=re.findall(r'depends on axioms:\s*\[([^]]*)\]',line)
                self.assertEqual(len(rows),1,'unparseable axiom list: '+line)
                self.assertLessEqual({s.strip() for s in rows[0].split(',') if s.strip()},
                                     ALLOWED,'unauthorized transitive axiom: '+line)

    def test_actual_optimum_witness_and_axioms(self):
        self._positive(_optimal())

    def test_actual_farkas_infeasibility_witness_and_axioms(self):
        self._positive(_farkas())

    def test_mutated_objective_breaks_genuine_optimum_proof(self):
        code,_=_optimal()
        line=next(l for l in code.splitlines() if l.startswith('def c :'))
        self.assertIn('(1 : ℚ)',line)
        changed=code.replace(line,'def c : Fin 2 → ℚ := fun j => (2 : ℚ)',1)
        self.assertNotEqual(code,changed)
        exitcode,log=_compile(changed)
        self.assertNotEqual(exitcode,0,'invalid dual-feasibility witness accepted')
        for forbidden in ('unknown module','unknown identifier','failed to import','unexpected token','out of memory'):
            self.assertNotIn(forbidden,log.lower())
        self.assertIn('error:',log.lower())

    def test_mutated_farkas_bound_breaks_genuine_infeasibility_proof(self):
        code,_=_farkas()
        line=next(l for l in code.splitlines() if l.startswith('def b :'))
        changed=code.replace(line,'def b : Fin 1 → ℚ := fun i => (1 : ℚ)',1)
        self.assertNotEqual(code,changed)
        exitcode,log=_compile(changed)
        self.assertNotEqual(exitcode,0,'false negative bound accepted')
        for forbidden in ('unknown module','unknown identifier','failed to import','unexpected token','out of memory'):
            self.assertNotIn(forbidden,log.lower())
        self.assertIn('error:',log.lower())


if __name__=='__main__':unittest.main()
