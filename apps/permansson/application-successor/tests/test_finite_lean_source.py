"""Fail-closed finite-world application/Lean source-binding regressions.

Passing here certifies correct bounded source emission and byte identity only.
No mock compiler is treated as a genuine proof or axiom audit.
"""
from __future__ import annotations

from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

APP = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(APP / 'src'))
from permansson_app.errors import AppError
from permansson_app.finite_world import parse_finite_world
from permansson_app.proof.finite_emit import emit_source, emit_file, rational_expr, indexed
from permansson_app.proof.finite_source_check import check_files
from permansson_app.strict_json import strict_loads

PACKAGE_EXAMPLE = APP / 'src/permansson_app/data/examples/finite_world.v1.model.json'


def load_example():
    return json.loads(PACKAGE_EXAMPLE.read_text(encoding='utf-8'))


class FiniteLeanReificationTests(unittest.TestCase):
    def test_canonical_source_complete_and_not_certified(self):
        source, receipt = emit_source(parse_finite_world(load_example()))
        self.assertIn('import PermanssonResearch.ApplicationBridge.FiniteWorldInput', source)
        self.assertIn('induced_rows_normalized', source)
        self.assertIn('input.inducedAtom', source)
        self.assertEqual(len(receipt['theorem_names']), 17)
        self.assertEqual(receipt['number_of_induced_atoms'], 16)
        self.assertEqual(receipt['p_u_infeasible_normalized_extensions'], [])
        self.assertFalse(receipt['lean_compiler_executed'])
        self.assertEqual(receipt['lean_status'], 'NOT_EXECUTED')
        self.assertFalse(receipt['scientific_claims_verified'])
        self.assertFalse(receipt['release_authorized'])
        self.assertNotIn('sorry', source)
        self.assertNotIn('native_decide', source)
        self.assertNotIn('admit', source)
        self.assertNotIn('\naxiom ', source)

    def test_input_row_reordering_stabilizes_semantic_lean_source(self):
        first = load_example()
        second = deepcopy(first)
        for key in ['feasible', 'alpha', 'P', 'U']:
            second[key].reverse()
        self.assertEqual(emit_source(parse_finite_world(first)), emit_source(parse_finite_world(second)))

    def test_mutated_source_primitives_change_reified_source(self):
        baseline = load_example()
        mutated = deepcopy(baseline)
        mutated['alpha'][0]['weights']['stay'] = '1'
        mutated['alpha'][0]['weights']['switch'] = '0'
        c = deepcopy(baseline)
        row = next(r for r in c['P'] if r['s']=='s0' and r['x']=='x0' and r['a']=='stay')
        row['weights']={'x0':'0','x1':'1'}
        d = deepcopy(baseline)
        row = next(r for r in d['U'] if r['s']=='s0' and r['x']=='x0' and r['a']=='stay' and r['xp']=='x0')
        row['weights']={'s0':'0','s1':'1'}
        base_source, base_receipt = emit_source(parse_finite_world(baseline))
        for changed in (mutated,c,d):
            source,receipt = emit_source(parse_finite_world(changed))
            self.assertNotEqual(source,base_source)
            self.assertNotEqual(receipt['lean_source_sha256'],base_receipt['lean_source_sha256'])

    def test_infeasible_rows_explicit_extension_not_source_data(self):
        m = load_example()
        row=next(r for r in m['feasible'] if r['s']=='s0' and r['x']=='x0')
        row['actions']=['stay']
        weights=next(r for r in m['alpha'] if r['s']=='s0' and r['x']=='x0')['weights']
        weights['stay']='1';weights['switch']='0'
        m['P']=[r for r in m['P'] if not (r['s']=='s0' and r['x']=='x0' and r['a']=='switch')]
        m['U']=[r for r in m['U'] if not (r['s']=='s0' and r['x']=='x0' and r['a']=='switch')]
        source,receipt=emit_source(parse_finite_world(m))
        self.assertEqual(len(receipt['p_u_infeasible_normalized_extensions']),1)
        self.assertEqual(receipt['p_u_infeasible_normalized_extensions'][0]['world_extension'],'dirac_same_world')
        self.assertIn('Infeasible P/U entries are normalized Dirac extensions.',source)
        self.assertEqual(receipt['lean_status'],'NOT_EXECUTED')

    def test_reject_nonstochastic_and_foreign_rows(self):
        for key in ('alpha','P','U'):
            m=load_example()
            m[key][0]['weights'][next(iter(m[key][0]['weights']))]='5/4'
            with self.subTest(key=key),self.assertRaises(AppError):
                parse_finite_world(m)
        m=load_example();m['P'].append(deepcopy(m['P'][0]))
        with self.assertRaises(AppError):parse_finite_world(m)

    def test_reject_oversized_dimensions_without_generating_unbounded_source(self):
        m=load_example()
        m['states']['strategic']=['s0','s1','s2']
        # Parser rejects missing rows even before literal-source bound.
        with self.assertRaises(AppError):parse_finite_world(m)
        # The reifier has its own stricter bound, verified on a valid 3-state model.
        m = load_example()
        m['states']['actions'].append('idle')
        for row in m['feasible']:
            row['actions'].append('idle')
        for row in m['alpha']:
            row['weights']['idle']='0'
        for row in list(m['P']):
            if row['a'] != 'stay':continue
            cloned=deepcopy(row);cloned['a']='idle';m['P'].append(cloned)
        for row in list(m['U']):
            if row['a'] != 'stay':continue
            cloned=deepcopy(row);cloned['a']='idle';m['U'].append(cloned)
        model=parse_finite_world(m)
        with self.assertRaises(AppError) as context: emit_source(model)
        self.assertEqual(context.exception.code,'REIFICATION_SCOPE')

    def test_index_and_rational_tokens_are_never_user_code(self):
        self.assertEqual(rational_expr(Fraction(-3,4)),'((-3 : ℚ) / (4 : ℚ))')
        self.assertEqual(indexed('x',['true'],1),'true')
        with self.assertRaises(AppError):indexed('x',['a','b'],1)
        m=load_example()
        m['states']['actions'][0]='foo\n#eval unsafe'
        with self.assertRaises(AppError):parse_finite_world(m)

    def test_emit_verify_then_source_and_metadata_tamper_fail(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td)
            m=root/'model.json';m.write_text(json.dumps(load_example()),encoding='utf-8')
            out=root/'proof'
            result=emit_file(m,out)
            check=check_files(m,out)
            self.assertEqual(result['lean_status'],'NOT_EXECUTED')
            self.assertEqual(check['status'],'SOURCE_BYTES_MATCH_NOT_LEAN_PROOF')
            self.assertEqual(check['theorem_count'],17)
            source_file=out/'ReifiedFiniteWorld.lean'
            source=source_file.read_text()
            source_file.write_text(source.replace('input.inducedAtom','input.invalidAtom',1))
            with self.assertRaises(AppError) as context:check_files(m,out)
            self.assertEqual(context.exception.code,'REIFICATION_SOURCE')
            source_file.write_text(source)
            receipt=out/'source_candidate.json';text=receipt.read_text()
            receipt.write_text(text.replace('NOT_EXECUTED','PASSED'))
            with self.assertRaises(AppError) as context:check_files(m,out)
            self.assertEqual(context.exception.code,'REIFICATION_RECEIPT')

    def test_source_model_tamper_rejected(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);model=root/'model.json'
            sample=load_example();model.write_text(json.dumps(sample))
            out=root/'proof';emit_file(model,out)
            sample['alpha'][0]['weights']={'stay':'0','switch':'1'}
            model.write_text(json.dumps(sample))
            with self.assertRaises(AppError):check_files(model,out)

    def test_duplicate_json_keys_and_output_scope_fail_closed(self):
        with self.assertRaises(AppError):strict_loads(b'{"a":1,"a":2}')
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);model=root/'model.json';model.write_text(json.dumps(load_example()))
            output=root/'proof';emit_file(model,output)
            with self.assertRaises(AppError) as context:emit_file(model,output)
            self.assertEqual(context.exception.code,'OUTPUT_SCOPE')
            symlink=root/'link';symlink.symlink_to(output,target_is_directory=True)
            with self.assertRaises(AppError):check_files(model,symlink)

    def test_actual_cli_source_generation_and_guard(self):
        with tempfile.TemporaryDirectory() as td:
            root=Path(td);model=root/'model.json';model.write_text(json.dumps(load_example()))
            directory=root/'out'
            proc=subprocess.run([sys.executable,'-B','-m','permansson_app.proof.finite_emit',
                                 str(model),'--output',str(directory)],
                                cwd=APP,env={'PYTHONPATH':str(APP/'src')},capture_output=True,text=True,timeout=20)
            self.assertEqual(proc.returncode,0,proc.stderr)
            check=subprocess.run([sys.executable,'-B','-m','permansson_app.proof.finite_source_check',
                                 str(model),str(directory)],
                                 cwd=APP,env={'PYTHONPATH':str(APP/'src')},capture_output=True,text=True,timeout=20)
            self.assertEqual(check.returncode,0,check.stderr)
            self.assertIn('SOURCE_BYTES_MATCH_NOT_LEAN_PROOF',check.stdout)

if __name__=='__main__':unittest.main()
