"""Checked admitted patch-grammar receipt -> source-bound Lean theorem *candidate*.

Only receipts that pass the independent grammar checker are emitted. The
baseline and every admitted block's treated model are reflected as
`FiniteWorldInput`s; each block is proved to keep feasibility and P and to be
the baseline with exactly its declared α/U patch rows. Lean decides every
block value, the inclusion-minimal positive blocks and the four-corner
interactions; the theorems identify them with actual path-law probabilities.
Only declared blocks are admissible (no downward closure). A positive finite
effect is not a constitutive or PR certificate. Emission is never compiler
replay, independent certification, empirical identification or release
acceptance.
"""
from __future__ import annotations
import argparse
from hashlib import sha256
import json
from pathlib import Path
import sys

from ..engines.grammar import apply_block, parse_grammar
from ..errors import AppError
from ..finite_world import exact_result
from ..identity import canonical_bytes
from ..receipts.grammar import check_grammar
from ..strict_json import strict_read
from .control_emit import _fin_case, _finset, _new_dir
from .finite_emit import input_definition, rational_expr

FORMAT='Permansson.App.GrammarLeanSourceCandidate.v1'
MODULE='PermanssonResearch.ApplicationBridge.ReifiedGrammar'
MAX_BLOCKS=8
MAX_HORIZON=6
MAX_SOURCE_BYTES=512*1024


def _override(rows:list[tuple[list[str],list[str]]],default:str)->str:
    """Nested `if guard then value else …` ending in `default`."""
    result=default
    for guards,value in reversed(rows):
        result=f'(if {" ∧ ".join(guards)} then {value} else {result})'
    return result


def block_definitions(g,ns:int,nx:int,na:int)->tuple[list[str],list[str],dict]:
    """Every admitted block's reflected treated model, with theorems that it keeps
    feasibility and P and is the baseline with exactly its declared patch rows."""
    S,X,A=list(g.baseline.strategic),list(g.baseline.world),list(g.baseline.actions)
    lines=[];names=[];extensions={}
    for i,block in enumerate(g.blocks):
        treated=apply_block(g,block)
        block_lines,dims,ext=input_definition(treated,f'block_{i}')
        if dims!=(ns,nx,na):raise AppError('GRAMMAR_REIFY_SCOPE','blocks must share the baseline dimensions')
        extensions[f'block_{i}']=ext
        alpha_rows=[];update_rows=[]
        for name in block:
            for key,vals in g.patch_rows[name].items():
                values=[rational_expr(exact_result(v)) for v in vals]
                if key[0]=='alpha':
                    s,x=key[1],key[2]
                    alpha_rows.append(([f's = ({S.index(s)} : Fin {ns})',f'x = ({X.index(x)} : Fin {nx})'],
                                       _fin_case('a',values,na)))
                else:
                    s,x,a,xp=key[1:]
                    update_rows.append(([f's = ({S.index(s)} : Fin {ns})',f'x = ({X.index(x)} : Fin {nx})',
                                         f'a = ({A.index(a)} : Fin {na})',f'xp = ({X.index(xp)} : Fin {nx})'],
                                        _fin_case('sp',values,ns)))
        label='{'+', '.join(block)+'}'
        lines+=[*block_lines,'',
                f'/-- Admitted block {i} = {label}: feasibility and P held fixed. -/',
                f'theorem block_{i}_held_fixed : HeldFixed base block_{i} := by',
                '  unfold HeldFixed',
                f'  simp only [base, block_{i}]',
                '  decide +kernel',
                f'/-- Block {i} is the baseline with exactly its declared α patch rows. -/',
                f'theorem block_{i}_alpha_rows : ∀ s x a, block_{i}.alpha s x a =',
                f'    {_override(alpha_rows,"base.alpha s x a")} := by',
                f'  simp only [base, block_{i}]',
                '  decide +kernel',
                f'/-- Block {i} is the baseline with exactly its declared U patch rows. -/',
                f'theorem block_{i}_update_rows : ∀ s x a xp sp, block_{i}.update s x a xp sp =',
                f'    {_override(update_rows,"base.update s x a xp sp")} := by',
                f'  simp only [base, block_{i}]',
                '  decide +kernel','']
        names+=[f'block_{i}_held_fixed',f'block_{i}_alpha_rows',f'block_{i}_update_rows']
    return lines,names,extensions


def emit_source(raw:dict,receipt:dict)->tuple[str,dict]:
    if type(raw) is not dict or type(receipt) is not dict:
        raise AppError('GRAMMAR_REIFY_INPUT','raw grammar request and receipt required')
    checked=check_grammar(raw,receipt)
    g=parse_grammar(raw)
    if len(g.blocks)>MAX_BLOCKS or not g.horizon<=MAX_HORIZON:
        raise AppError('GRAMMAR_REIFY_SCOPE',
                       f'Lean grammar reflection limited to {MAX_BLOCKS} blocks and horizon 0..{MAX_HORIZON}')
    m=g.baseline
    base_lines,(ns,nx,na),base_ext=input_definition(m,'base')
    N=ns*nx
    ids=list(g.patch_targets);C=len(ids)
    S,X,A=list(m.strategic),list(m.world),list(m.actions)
    states=[(s,x) for s in S for x in X]
    survival=g.value_type=='survival_horizon'
    k=len(g.blocks)
    results={tuple(r['component_ids']):r for r in receipt['block_results']}
    zero=exact_result('0')

    def vector(values):
        full=[zero]*N
        for x,v in zip(g.comparison,values):full[x]=exact_result(v)
        return _fin_case('y',[rational_expr(v) for v in full],N)

    dim=f'({ns} * {nx})'
    lines=[
        'import PermanssonResearch.ApplicationBridge.GrammarReceipt',
        'import Mathlib.Tactic','',
        '/-! Reified exact admitted patch-grammar receipt; application source candidate only.',
        f'    Request identity SHA-256: {receipt["request_identity"]["sha256"]}',
        f'    Independently checked receipt SHA-256: {checked["receipt_sha256"]}',
        '    Only declared blocks are admissible; P is held fixed. A positive finite',
        '    effect is not a constitutive or PR certificate.',
        '    A compiler result and independent review are NOT asserted. -/','',
        f'namespace {MODULE}',
        'open MeasureTheory',
        'open PermanssonResearch.ApplicationBridge',
        'open PermanssonResearch.ApplicationBridge.ControlTableReceipt',
        'open PermanssonResearch.ApplicationBridge.MenuReceipt',
        'open PermanssonResearch.ApplicationBridge.GrammarReceipt',
        'open PermanssonResearch.ReverseSolver',
        'set_option autoImplicit false',
        'set_option maxRecDepth 8192',
        'set_option maxHeartbeats 0','',
        *base_lines,'',
    ]
    block_src,names,block_ext=block_definitions(g,ns,nx,na)
    lines+=block_src
    extensions={'base':base_ext,**block_ext}
    index={b:i for i,b in enumerate(g.blocks)}
    minimal=[index[tuple(b)] for b in receipt['minimal_positive_blocks']]
    corner_terms=[]
    for a,u in g.four_corners:
        joint=tuple(x for x in ids if x in (a,u))
        corner_terms.append(f'⟨{index[()]}, {index[(a,)]}, {index[(u,)]}, {index[joint]}, '
                            f'{ids.index(a)}, {ids.index(u)}⟩')
    interactions=[vector(c['interactions_by_comparison_state']) for c in receipt['four_corners']]
    members=_fin_case('i',[f'inducedMatrix block_{i}' for i in range(k)],k)
    blocks_body=_fin_case('i',[_finset([ids.index(x) for x in b],C) for b in g.blocks],k)
    values_body=_fin_case('i',[vector(results[b]['values_by_comparison_state']) for b in g.blocks],k)
    lines+=[
        f'def baseMatrix : RationalMarkovMatrix {dim} := inducedMatrix base',
        f'def members : Fin {k} → RationalMarkovMatrix {dim} := fun i => {members}',
        f'def blocks : Fin {k} → Finset (Fin {C}) := fun i => {blocks_body}',
        f'def region : Finset (Fin {dim}) := {_finset(list(g.region),N)}',
        f'def horizon : ℕ := {g.horizon}',
        f'def survival : Bool := {"true" if survival else "false"}',
        f'def comparison : Finset (Fin {dim}) := {_finset(list(g.comparison),N)}',
        f'def baseValues : Fin {dim} → ℚ := fun y => {vector(receipt["baseline_values"])}',
        f'def values : Fin {k} → Fin {dim} → ℚ := fun i y => {values_body}',
        f'def minimal : Finset (Fin {k}) := {_finset(sorted(minimal),k)}',
        f'def corners : List (Corner {k} {C}) := [{", ".join(corner_terms)}]',
        f'def interactions : ℕ → Fin {dim} → ℚ := fun r y => '
        + ''.join(f'(if r = {r} then {body} else ' for r,body in enumerate(interactions))
        + '(0 : ℚ)' + ')'*len(interactions),
        '',
        '/-- Kernel evaluation of block values, minimal positive blocks and corners. -/',
        'theorem receipt_checked :',
        '    checkAdmittedBlocks baseMatrix members blocks region horizon survival comparison',
        '      baseValues values minimal corners interactions = true := by',
        '  decide +kernel','',
        '/-- The minimal set is exactly the admitted blocks whose actual effect is positive',
        '    on the whole comparison set and that contain no smaller such admitted block. -/',
        f'theorem minimal_positive_blocks : ∀ i : Fin {k}, i ∈ minimal ↔',
        '    ((∀ x ∈ comparison, actualObjective baseMatrix region horizon survival x <',
        '        actualObjective (members i) region horizon survival x) ∧',
        '      ∀ j, blocks j ⊂ blocks i →',
        '        ¬ ∀ x ∈ comparison, actualObjective baseMatrix region horizon survival x <',
        '          actualObjective (members j) region horizon survival x) :=',
        '  checked_minimal_positive_blocks baseMatrix members blocks region horizon survival',
        '    comparison baseValues values minimal corners interactions receipt_checked','',
    ]
    names+=['receipt_checked','minimal_positive_blocks']
    args=('baseMatrix members blocks region horizon survival comparison baseValues values minimal '
          'corners interactions receipt_checked')
    for i,b in enumerate(g.blocks):
        for x,v in zip(g.comparison,results[b]['values_by_comparison_state']):
            name=f'block_value_{i}_{x}'
            names.append(name)
            lines+=[f'theorem {name} :',
                    f'    actualObjective (members {i}) region horizon survival ({x} : Fin {N}) =',
                    f'      (({rational_expr(exact_result(v))} : ℚ) : ℝ) := by',
                    f'  rw [← checked_block_value_actual {args} {i} ({x} : Fin {N}) (by decide +kernel)]',
                    f'  have hv : values {i} ({x} : Fin {N}) = {rational_expr(exact_result(v))} := by decide +kernel',
                    '  rw [hv]','']
    objective=lambda i,x:f'actualObjective (members {i}) region horizon survival ({x} : Fin {N})'
    for r,(corner,(a,u)) in enumerate(zip(receipt['four_corners'],g.four_corners)):
        joint=tuple(x for x in ids if x in (a,u))
        i0,ia,iu,ij=index[()],index[(a,)],index[(u,)],index[joint]
        for x,v in zip(g.comparison,corner['interactions_by_comparison_state']):
            name=f'four_corner_{r}_{x}'
            names.append(name)
            value=rational_expr(exact_result(v))
            lines+=[f'/-- Interaction of `{a}` and `{u}` from state {x}: actual probabilities. -/',
                    f'theorem {name} :',
                    f'    {objective(ij,x)} - {objective(ia,x)} -',
                    f'      {objective(iu,x)} + {objective(i0,x)} = (({value} : ℚ) : ℝ) := by',
                    f'  have h := checked_four_corner_effects {args} ⟨{r}, by decide⟩ ({x} : Fin {N})',
                    '    (by decide +kernel)',
                    f'  have hv : interactions ((⟨{r}, by decide⟩ : Fin corners.length) : ℕ) ({x} : Fin {N}) =',
                    f'      {value} := by decide +kernel',
                    '  rw [hv] at h',
                    '  exact h.symm','']
    lines.append(f'end {MODULE}')
    lines.append('')
    for name in names:
        lines.append(f'#print axioms {MODULE}.{name}')
    lines.append('')
    text='\n'.join(lines)
    if len(text.encode('utf-8'))>MAX_SOURCE_BYTES:
        raise AppError('GRAMMAR_REIFY_SCOPE','generated Lean source exceeds byte limit')
    out={
        'format':FORMAT,
        'problem_semantic_identity':receipt['request_identity'],
        'receipt_sha256':checked['receipt_sha256'],
        'theorem_names':names,
        'theorem_qualified_names':[MODULE+'.'+n for n in names],
        'theorem_module':MODULE,
        'lean_source_sha256':sha256(text.encode('utf-8')).hexdigest(),
        'scope':{'ns':ns,'nx':nx,'na':na,'joint_states':N,'blocks':[list(b) for b in g.blocks],
                 'horizon':g.horizon,'value_type':g.value_type,
                 'admission':'EXACT_DECLARED_BLOCKS_ONLY_NO_DOWNWARD_CLOSURE',
                 'interpretation':'FINITE_EFFECT_NOT_CONSTITUTIVE_OR_PR_CERTIFICATE'},
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
    (destination/'ReifiedGrammar.lean').write_bytes(lean.encode('utf-8'))
    (destination/'source_candidate.json').write_bytes(canonical_bytes(metadata)+b'\n')
    return {'format':FORMAT,'source_file':str(destination/'ReifiedGrammar.lean'),
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
