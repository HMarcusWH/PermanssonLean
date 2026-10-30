"""Checked typed quotient receipt -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent quotient checker are emitted. The
baseline and every declared intervention are reflected as `FiniteWorldInput`s
(interventions are proved to hold feasibility, P and the undeclared generator
fixed); each profile's coarse matrix is checked to be a complete strong
lumping of that profile's α/P/U-induced matrix along the reflected projection.
The theorems identify the fine and coarse finite-horizon survival (or exit)
values with actual path-law probabilities and prove they agree. No coarse
α/P/U decomposition, approximate bisimulation, GR/PR status or causal
identification is claimed. Emission is never compiler replay, independent
certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.quotients import parse_quotient
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes
from ..receipts.quotients import check_quotient
from ..strict_json import strict_read
from .control_emit import _fin_case, _finset, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.QuotientLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedQuotient'
MAX_PROFILES=4
MAX_HORIZON=6
MAX_SOURCE_BYTES=512*1024


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('QUOTIENT_REIFY_INPUT','raw quotient request and receipt required')
    checked=check_quotient(raw,receipt)
    q=parse_quotient(raw)
    if not q.horizon<=MAX_HORIZON or len(q.interventions)+1>MAX_PROFILES:
        raise AppError('QUOTIENT_REIFY_SCOPE',
                       f'Lean quotient reflection limited to horizon 0..{MAX_HORIZON} and {MAX_PROFILES} profiles')
    models=[('base',q.baseline,'baseline')]+[(f'member_{i}',model,target)
                                              for i,(tag,target,model) in enumerate(q.interventions)]
    definitions=[];extensions={}
    for name,model,_ in models:
        lines_i,dims,ext=input_definition(model,name)
        definitions.append((name,lines_i,dims));extensions[name]=ext
    ns,nx,na=definitions[0][2]
    if any(dims!=(ns,nx,na) for _,_,dims in definitions):
        raise AppError('QUOTIENT_REIFY_SCOPE','interventions must share the baseline dimensions')
    N=ns*nx;M=len(q.coarse_states)
    survival=q.value_type=='survival_horizon'
    profiles=receipt['profiles']

    dim=f'({ns} * {nx})'
    lines=[
        'import PermanssonResearch.ApplicationBridge.QuotientReceipt',
        'import PermanssonResearch.ApplicationBridge.MenuReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact typed quotient receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Exact strong lumpability of each declared profile; finite-horizon transport only.',
        '    No coarse alpha/P/U decomposition, GR/PR or causal claim.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open MeasureTheory',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.MenuReceipt',
        'open PermanssonResearch.ApplicationBridge.ExitReceipt',
        'open PermanssonResearch.ApplicationBridge.QuotientReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.FiniteStrategicRealization',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
    ]
    names=[]
    for (name,lines_i,_),(_,_,target) in zip(definitions,models):
        lines+=[*lines_i,'']
        if name=='base':continue
        lines+=[f'/-- Declared intervention (target: {target}). -/',
                f'theorem {name}_held_fixed : HeldFixed base {name} := by',
                '  unfold HeldFixed',
                f'  simp only [base, {name}]',
                '  decide +kernel']
        names.append(f'{name}_held_fixed')
        if target=='alpha':
            lines+=[f'theorem {name}_update_held_fixed :',
                    f'    ∀ s x a xp sp, {name}.update s x a xp sp = base.update s x a xp sp := by',
                    f'  simp only [base, {name}]','  decide +kernel']
            names.append(f'{name}_update_held_fixed')
        elif target=='U':
            lines+=[f'theorem {name}_alpha_held_fixed :',
                    f'    ∀ s x a, {name}.alpha s x a = base.alpha s x a := by',
                    f'  simp only [base, {name}]','  decide +kernel']
            names.append(f'{name}_alpha_held_fixed')
        lines.append('')
    lines+=[
        f'def proj : Fin {dim} → Fin {M} := fun y => {_fin_case("y",[f"({c} : Fin {M})" for c in q.coarse_index],N)}',
        f'def region : Finset (Fin {dim}) := {_finset(list(q.region),N)}',
        f'def coarseRegion : Finset (Fin {M}) := {_finset(list(q.coarse_region),M)}',
        f'def comparison : Finset (Fin {dim}) := {_finset(list(q.comparison),N)}',
        f'def horizon : ℕ := {q.horizon}',
        f'def survival : Bool := {"true" if survival else "false"}','',
    ]
    for p,(name,_,_) in enumerate(definitions):
        profile=profiles[p]
        coarse_rows=[[exact_ratio(v,probability=True) for v in row] for row in profile['coarse_kernel']]
        fine_vals=[exact_ratio(v,probability=True) for v in profile['fine_values']]
        coarse_vals=[exact_ratio(v,probability=True) for v in profile['coarse_values']]
        fine_full=[fine_vals[q.comparison.index(x)] if x in q.comparison else exact_ratio('0') for x in range(N)]
        coarse_full=[coarse_vals[q.coarse_comparison.index(c)] if c in q.coarse_comparison else exact_ratio('0')
                     for c in range(M)]
        entry=_fin_case('c',[_fin_case('d',[rational_expr(v) for v in row],M) for row in coarse_rows],M)
        lines+=[
            f'/-- Profile `{profile["id"]}`: fine induced matrix and its reported coarse matrix. -/',
            f'def K_{p} : RationalMarkovMatrix {dim} := inducedMatrix {name}',
            f'def Q_{p} : RationalMarkovMatrix {M} where',
            f'  entry := fun c d => {entry}',
            '  entry_nonneg := by decide +kernel',
            '  row_sum_one := by decide +kernel',
            f'def fine_{p} : Fin {dim} → ℚ := fun y => {_fin_case("y",[rational_expr(v) for v in fine_full],N)}',
            f'def coarse_{p} : Fin {M} → ℚ := fun c => {_fin_case("c",[rational_expr(v) for v in coarse_full],M)}',
            '',
            f'/-- Kernel evaluation: strong lumpability, fiber region and both value tables. -/',
            f'theorem profile_{p}_checked :',
            f'    checkQuotientProfile K_{p} Q_{p} proj region coarseRegion horizon survival comparison',
            f'      fine_{p} coarse_{p} = true := by',
            '  decide +kernel','',
            f'/-- Fine and coarse actual region-survival probabilities agree for every start. -/',
            f'theorem transport_{p} : ∀ x : Fin {dim},',
            f'    ((realizedModel K_{p}).pathLaw (Measure.dirac (decode x))).real (staysThrough region horizon) =',
            f'      ((realizedModel Q_{p}).pathLaw (Measure.dirac (decode (proj x)))).real',
            '        (staysThrough coarseRegion horizon) :=',
            f'  checked_quotient_transport K_{p} Q_{p} proj region coarseRegion horizon survival comparison',
            f'    fine_{p} coarse_{p} profile_{p}_checked','',
        ]
        names+=[f'profile_{p}_checked',f'transport_{p}']
        for x in q.comparison:
            v=fine_full[x]
            event=(f'((realizedModel K_{p}).pathLaw (Measure.dirac (decode ({x} : Fin {N})))).real '
                   '(staysThrough region horizon)')
            stated=event if survival else f'1 - {event}'
            name_v=f'value_{p}_{x}'
            names.append(name_v)
            lines+=[f'/-- Actual {"survival" if survival else "exit"} probability of profile {p} from state {x}. -/',
                    f'theorem {name_v} : {stated} = (({rational_expr(v)} : ℚ) : ℝ) := by',
                    f'  have h := checked_fine_value_actual K_{p} Q_{p} proj region coarseRegion horizon survival',
                    f'    comparison fine_{p} coarse_{p} profile_{p}_checked ({x} : Fin {N}) (by decide +kernel)',
                    f'  have hv : fine_{p} ({x} : Fin {N}) = {rational_expr(v)} := by decide +kernel',
                    '  rw [hv] at h',
                    ('  simp only [survival, ↓reduceIte] at h' if survival else
                     '  simp only [survival, Bool.false_eq_true, ↓reduceIte] at h'),
                    '  exact h.symm','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('QUOTIENT_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':receipt['request_identity'],
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'coarse_states':M,
                 'profiles':[p['id'] for p in profiles],'horizon':q.horizon,
                 'value_type':q.value_type,
                 'interpretation':'EXACT_STRONG_LUMPABILITY_FINITE_HORIZON_TRANSPORT_ONLY'},
        'p_u_infeasible_normalized_extensions':extensions,
        'lean_status':'NOT_EXECUTED',
        'source_emitted':True,
        'compiler_evidence_authenticated':False,
        'independent_math_certification':False,
        'empirical_identification':False,
        'application_release_authorized':False,
    }
    return text,out


def emit_files(request_file:Path,receipt_file:Path,out_dir:Path)->dict:
    request_raw,request=strict_read(request_file)
    receipt_raw,receipt=strict_read(receipt_file)
    lean,metadata=emit_source(request,receipt)
    metadata['problem_bytes_sha256']=sha256(request_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedQuotient.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedQuotient.lean'),
            'metadata_file':str(destination/'source_candidate.json'),
            'lean_status':'NOT_EXECUTED','candidate_sha256':metadata['lean_source_sha256']}


def main(argv=None)->int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('request',type=Path)
    parser.add_argument('receipt',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    try:
        print(json.dumps(emit_files(args.request,args.receipt,args.output),sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok':False,'error':{'code':exc.code,'message':str(exc)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__=='__main__':
    raise SystemExit(main())
