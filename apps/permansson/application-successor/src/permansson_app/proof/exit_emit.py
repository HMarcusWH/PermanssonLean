"""Checked first-exit routing receipt -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent exit checker are emitted. The model is
reflected as a `FiniteWorldInput` (`K := inducedMatrix input`). The emitted
theorems identify, for every start in the region, the survival table, the
cumulative first-exit table per destination, the eventual first-exit
probability per destination and the never-exit mass with events of the actual
infinite path law. Eventual routing is certified through a Dirichlet
certificate of the exit-stopped chain, computed here as untrusted data and
checked by Lean. Nothing is normalized. Restart laws, switch retention and
GR/PR statements are not claimed. Emission is never compiler replay,
independent certification, empirical identification or release acceptance.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.exit import parse_region
from ..engines.occupation import bottom_classes
from ..engines.rational_linear import solve_unique
from ..errors import AppError
from ..finite_world import exact_result,induced_kernel,parse_finite_world
from ..identity import canonical_bytes
from ..receipts.exit import check_exit
from ..strict_json import strict_read, read_result
from .control_emit import _fin_case, _finset, _nat_case, _new_dir
from .finite_emit import input_definition, rational_expr
from .occupation_emit import _by_class

FORMAT='Permansson.App.ExitLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedExit'
MAX_HORIZON=6
MAX_SOURCE_BYTES=512*1024


def stopped_certificate(K,region):
    """Bottom classes and absorption weights of the exit-stopped chain.

    Untrusted certificate data: Lean's `checkDirichlet` decides it.
    """
    n=len(K);inside=set(region)
    stopped=tuple(tuple(K[y][z] if y in inside else Fraction(int(z==y)) for z in range(n))
                  for y in range(n))
    classes=[list(c) for c in bottom_classes(stopped)]
    recurrent={i for c in classes for i in c}
    transient=[i for i in range(n) if i not in recurrent]
    weights=[]
    for c in classes:
        column=[Fraction(int(i in c)) for i in range(n)]
        if transient:
            A=[[Fraction(int(i==j))-stopped[i][j] for j in transient] for i in transient]
            b=[sum((stopped[i][j] for j in c),Fraction(0)) for i in transient]
            for i,value in zip(transient,solve_unique(A,b)):column[i]=value
        weights.append(column)
    return classes,weights


def emit_source(raw_model:dict,raw_region:dict,receipt:dict)->tuple[str,dict]:
    if type(raw_model) is not dict or type(raw_region) is not dict or type(receipt) is not dict:
        raise AppError('EXIT_REIFY_INPUT','raw finite model, region and exit receipt required')
    model=parse_finite_world(raw_model)
    region=parse_region(raw_region,model)
    checked=check_exit(model,region,receipt)
    H=region.horizon
    if not H<=MAX_HORIZON:
        raise AppError('EXIT_REIFY_SCOPE',f'Lean exit reflection limited to 0..{MAX_HORIZON} transitions')
    input_lines,(ns,nx,na),extensions=input_definition(model)
    N=ns*nx
    B=list(region.joint_indices);outside=list(receipt['outside_indices'])
    rows={row['start_index']:row for row in receipt['rows']}
    zero=Fraction(0)
    survival=[[zero]*N for _ in range(H+1)]
    steps=[[[zero]*N for _ in range(N)] for _ in range(H)]
    eventual=[[zero]*N for _ in range(N)]
    never=[zero]*N
    for x in B:
        row=rows[x]
        for t,v in enumerate(row['survival_through']):
            survival[t][x]=exact_result(v,probability=True)
        for s,step in enumerate(row['first_exit_by_step_and_destination']):
            for d,v in zip(outside,step):steps[s][x][d]=exact_result(v,probability=True)
        for d,v in zip(outside,row['eventual_exit_by_destination']):
            eventual[x][d]=exact_result(v,probability=True)
        never[x]=exact_result(row['never_exit'],probability=True)
    classes,weights=stopped_certificate(induced_kernel(model),B)

    dim=f'({ns} * {nx})'
    def vector(var,values):return _fin_case(var,[rational_expr(v) for v in values],N)
    weight_body=_by_class(classes,[vector('x',column) for column in weights],'(0 : ℚ)')
    class_names=', '.join(f'class_{c}' for c in range(len(classes)))
    lines=[
        'import PermanssonResearch.ApplicationBridge.ExitReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact first-exit routing receipt; application source candidate only.',
        f'    Model identity SHA-256: {receipt["model_semantic_identity"]["sha256"]}',
        f'    Region identity SHA-256: {receipt["region_semantic_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Infeasible P/U entries are normalized Dirac extensions. Exit routing is a',
        '    subprobability; the never-exit mass is separate. The stopped-chain',
        '    Dirichlet certificate is untrusted data decided by the kernel.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open MeasureTheory',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.ExitReceipt',
        'open PermanssonResearch.ReverseSolver',
        'open PermanssonResearch.ReverseSolver.C10',
        'open PermanssonResearch.ReverseSolver.FiniteStrategicRealization',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *input_lines,'',
        f'instance : NeZero {dim} := ⟨by norm_num⟩',
        f'def K : RationalMarkovMatrix {dim} := inducedMatrix input',
        f'def region : Finset (Fin {dim}) := {_finset(B,N)}',
        f'def horizon : ℕ := {H}',
        f'def survival : ℕ → Fin {dim} → ℚ := fun t y => '
        f'{_nat_case("t",[vector("y",row) for row in survival],"(0 : ℚ)")}',
        f'def steps : ℕ → Fin {dim} → Fin {dim} → ℚ := fun s x d => '
        f'{_nat_case("s",[_fin_case("x",[vector("d",row) for row in step],N) for step in steps],"(0 : ℚ)")}',
    ]
    for c,group in enumerate(classes):
        lines.append(f'def class_{c} : Finset (Fin {dim}) := {_finset(group,N)}')
    lines+=[
        f'/-- Dirichlet certificate of the exit-stopped chain `stopOutside K region`. -/',
        f'def cert : DirichletCertificate {dim} where',
        f'  classes := {{{class_names}}}',
        f'  weight := fun C x => {weight_body}',
        f'def eventual : Fin {dim} → Fin {dim} → ℚ := fun x d => '
        f'{_fin_case("x",[vector("d",row) for row in eventual],N)}',
        f'def never : Fin {dim} → ℚ := fun x => {vector("x",never)}',
        '',
        '/-- Kernel evaluation of every table, the stopped-chain certificate,',
        '    eventual routing and never-exit mass. -/',
        'theorem receipt_checked :',
        '    checkExitRoutingReceipt K region horizon survival steps cert eventual never = true := by',
        '  decide +kernel','',
    ]
    names=['receipt_checked']
    args='K region horizon survival steps cert eventual never receipt_checked'
    law=lambda x:f'((realizedModel K).pathLaw (Measure.dirac (decode ({x} : Fin {N})))).real'
    for x in B:
        lines+=[f'/-- Actual probability of staying in the region through the horizon from state {x}. -/',
                f'theorem survival_{x} :',
                f'    {law(x)} (staysThrough region horizon) =',
                f'      (({rational_expr(survival[H][x])} : ℚ) : ℝ) := by',
                f'  rw [← checked_survival_actual {args} horizon le_rfl ({x} : Fin {N})',
                '    (by decide +kernel)]',
                f'  have hv : survival horizon ({x} : Fin {N}) = {rational_expr(survival[H][x])} := by',
                '    decide +kernel',
                '  rw [hv]','',
                f'/-- Actual probability of never leaving the region from state {x}. -/',
                f'theorem never_exit_{x} :',
                f'    {law(x)} (staysForever region) = (({rational_expr(never[x])} : ℚ) : ℝ) := by',
                f'  rw [← checked_never_exit_actual {args} ({x} : Fin {N}) (by decide +kernel)]',
                f'  have hv : never ({x} : Fin {N}) = {rational_expr(never[x])} := by decide +kernel',
                '  rw [hv]','']
        names+=[f'survival_{x}',f'never_exit_{x}']
        for d in outside:
            within=sum((steps[s][x][d] for s in range(H)),zero)
            lines+=[f'/-- First state outside the region is {d}, within the horizon, from {x}. -/',
                    f'theorem exit_within_horizon_{x}_{d} :',
                    f'    {law(x)} (firstExitBy region ({d} : Fin {N}) horizon) =',
                    f'      (({rational_expr(within)} : ℚ) : ℝ) := by',
                    f'  rw [← checked_exit_by_actual {args} horizon le_rfl ({x} : Fin {N})',
                    f'    (by decide +kernel) ({d} : Fin {N}) (by decide +kernel)]',
                    f'  have hv : (∑ s ∈ Finset.range horizon, steps s ({x} : Fin {N}) ({d} : Fin {N})) =',
                    f'      {rational_expr(within)} := by decide +kernel',
                    '  rw [hv]','',
                    f'/-- First state outside the region is {d}, eventually, from {x}. -/',
                    f'theorem eventual_exit_{x}_{d} :',
                    f'    {law(x)} (firstExitAt region ({d} : Fin {N})) =',
                    f'      (({rational_expr(eventual[x][d])} : ℚ) : ℝ) := by',
                    f'  rw [← checked_eventual_exit_actual {args} ({x} : Fin {N})',
                    f'    (by decide +kernel) ({d} : Fin {N}) (by decide +kernel)]',
                    f'  have hv : eventual ({x} : Fin {N}) ({d} : Fin {N}) = {rational_expr(eventual[x][d])} := by',
                    '    decide +kernel',
                    '  rw [hv]','']
            names+=[f'exit_within_horizon_{x}_{d}',f'eventual_exit_{x}_{d}']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('EXIT_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':{'model':receipt['model_semantic_identity'],
                                     'region':receipt['region_semantic_identity']},
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'horizon':H,
                 'region':B,'outside':outside,'stopped_chain_classes':classes,
                 'interpretation':'SUBPROBABILITY_ROUTING_PLUS_NEVER_EXIT_MASS',
                 'not_claimed':['restart_law','switch_retention','gr_pr']},
        'p_u_infeasible_normalized_extensions':extensions,
        'lean_status':'NOT_EXECUTED',
        'source_emitted':True,
        'compiler_evidence_authenticated':False,
        'independent_math_certification':False,
        'empirical_identification':False,
        'application_release_authorized':False,
    }
    return text,out


def emit_files(model_file:Path,region_file:Path,receipt_file:Path,out_dir:Path)->dict:
    model_raw,model=strict_read(model_file)
    region_raw,region=strict_read(region_file)
    receipt_raw,receipt=read_result(receipt_file)
    lean,metadata=emit_source(model,region,receipt)
    metadata['problem_bytes_sha256']=sha256(model_raw).hexdigest()
    metadata['region_bytes_sha256']=sha256(region_raw).hexdigest()
    metadata['receipt_bytes_sha256']=sha256(receipt_raw).hexdigest()
    destination=_new_dir(out_dir)
    (destination/'ReifiedExit.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedExit.lean'),
            'metadata_file':str(destination/'source_candidate.json'),
            'lean_status':'NOT_EXECUTED','candidate_sha256':metadata['lean_source_sha256']}


def main(argv=None)->int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('model',type=Path)
    parser.add_argument('region',type=Path)
    parser.add_argument('receipt',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args(argv)
    try:
        print(json.dumps(emit_files(args.model,args.region,args.receipt,args.output),sort_keys=True))
        return 0
    except AppError as exc:
        print(json.dumps({'ok':False,'error':{'code':exc.code,'message':str(exc)}},sort_keys=True),file=sys.stderr)
        return 2

if __name__=='__main__':
    raise SystemExit(main())
