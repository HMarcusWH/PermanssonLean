"""Exact finite alpha/U patch grammar and declared admissible-block effects.

Only *declared* blocks are admissible: downward closure is never assumed.
Each overlapping patch must agree on the actual complete stochastic row.
These numeric effects do not establish a generalized PR certificate.
"""
from __future__ import annotations
from copy import deepcopy
from dataclasses import dataclass
from fractions import Fraction
import re
from ..errors import AppError
from ..finite_world import parse_finite_world,FiniteWorld,exact_ratio,exact_result,induced_kernel,compare_strategic_intervention
from ..identity import rational_text,semantic_identity

FORMAT='Permansson.App.FiniteGrammarRequest.v1'
RECEIPT='Permansson.App.FiniteGrammarReceipt.v1'
LABEL=re.compile(r'^[A-Za-z][A-Za-z0-9_-]{0,31}$')

@dataclass(frozen=True)
class Grammar:
    baseline:FiniteWorld
    patch_rows:dict[str,dict]
    patch_targets:dict[str,str]
    blocks:tuple[tuple[str,...],...]
    region:tuple[int,...]
    comparison:tuple[int,...]
    horizon:int
    value_type:str
    four_corners:tuple[tuple[str,str],...]
    semantic_id:dict


def parse_grammar(raw:object)->Grammar:
    fields={'format','baseline','patches','admitted_blocks','region','comparison_states','horizon','value_type','four_corners'}
    if type(raw) is not dict or set(raw)!=fields or raw['format']!=FORMAT:
        raise AppError('GRAMMAR_INPUT','wrong finite grammar version or fields')
    m=parse_finite_world(raw['baseline'])
    states=tuple((s,x) for s in m.strategic for x in m.world)
    if len(states)>12 or type(raw['horizon']) is not int or not 0<=raw['horizon']<=16:
        raise AppError('GRAMMAR_SCOPE','max 12 joint states and 16 transitions')
    if raw['value_type'] not in ('exit_by_horizon','survival_horizon'):
        raise AppError('GRAMMAR_SCOPE','only finite exit/survival event supported')
    def state_set(key):
        v=raw[key]
        if type(v) is not list or not v or len(v)>len(states):
            raise AppError('GRAMMAR_REGION',f'{key} must be a bounded nonempty state set')
        idx=[]
        for row in v:
            if type(row) is not list or len(row)!=2 or any(type(a) is not str for a in row) or tuple(row) not in states or states.index(tuple(row)) in idx:
                raise AppError('GRAMMAR_REGION',f'{key} has invalid/duplicate state')
            idx.append(states.index(tuple(row)))
        return tuple(sorted(idx))
    region=state_set('region');selected=state_set('comparison_states')
    if not set(selected)<=set(region):
        raise AppError('GRAMMAR_REGION','comparison states must lie inside the region')
    patches=raw['patches']
    if type(patches) is not list or not 1<=len(patches)<=8:
        raise AppError('GRAMMAR_SCOPE','require 1..8 labelled patches')
    patch_rows={};patch_targets={};ids=[]
    for item in patches:
        if type(item) is not dict or set(item)!={'id','target','rows'}:
            raise AppError('GRAMMAR_PATCH','patch entry must specify id,target,rows')
        name=item['id'];target=item['target']
        if type(name) is not str or not LABEL.fullmatch(name) or name in ids or target not in ('alpha','U'):
            raise AppError('GRAMMAR_PATCH','invalid/duplicate patch ID or target')
        rows=item['rows']
        if type(rows) is not list or not 1<=len(rows)<=72:
            raise AppError('GRAMMAR_PATCH','patch must contain at least one bounded row')
        ids.append(name);patch_targets[name]=target;updates={}
        for row in rows:
            keys={'s','x','weights'} if target=='alpha' else {'s','x','a','xp','weights'}
            if type(row) is not dict or set(row)!=keys:
                raise AppError('GRAMMAR_PATCH','patch row has wrong source identity')
            k=('alpha',row['s'],row['x']) if target=='alpha' else ('U',row['s'],row['x'],row['a'],row['xp'])
            if any(type(v) is not str for v in k):raise AppError('GRAMMAR_PATCH','row identifiers must be strings')
            if (target=='alpha' and (row['s'],row['x']) not in m.alpha) or (target=='U' and (row['s'],row['x'],row['a'],row['xp']) not in m.U):
                raise AppError('GRAMMAR_PATCH','unknown/infeasible patch row')
            outputs=m.actions if target=='alpha' else m.strategic
            weights=row['weights']
            if type(weights) is not dict or set(weights)!=set(outputs):
                raise AppError('GRAMMAR_PATCH','patch must specify complete stochastic row')
            vals=tuple(exact_ratio(weights[a],probability=True) for a in outputs)
            if sum(vals,Fraction(0))!=1:raise AppError('GRAMMAR_PATCH','patch row not stochastic')
            if target=='alpha' and any(p>0 and a not in m.feasible[row['s'],row['x']] for a,p in zip(outputs,vals)):
                raise AppError('GRAMMAR_PATCH','patch assigns mass to infeasible action')
            if k in updates:raise AppError('GRAMMAR_PATCH','patch repeats a source row')
            updates[k]=tuple(rational_text(v) for v in vals)
        patch_rows[name]=updates
    admitted=raw['admitted_blocks']
    if type(admitted) is not list or not 1<=len(admitted)<=32:
        raise AppError('GRAMMAR_ADMISSION','bounded explicitly enumerated admitted blocks required')
    blocks=[]
    for block in admitted:
        if type(block) is not list or len(block)>len(ids) or any(type(x) is not str or x not in ids for x in block):
            raise AppError('GRAMMAR_ADMISSION','block references an undeclared component')
        ordered=tuple(x for x in ids if x in block)
        if tuple(block)!=ordered or len(set(block))!=len(block) or ordered in blocks:
            raise AppError('GRAMMAR_ADMISSION','block must have distinct components in declaration order')
        blocks.append(ordered)
    if () not in blocks:raise AppError('GRAMMAR_ADMISSION','empty baseline block is mandatory')
    # Only admitted composite blocks must have compatible overlaps. Nothing
    # assumes an unlisted subset has permission to run.
    for block in blocks:
        touched={}
        for id in block:
            for k,v in patch_rows[id].items():
                if k in touched and touched[k]!=v:
                    raise AppError('GRAMMAR_OVERLAP','admitted overlapping patches disagree on the same original row')
                touched[k]=v
    corners=raw['four_corners']
    if type(corners) is not list or len(corners)>8:raise AppError('GRAMMAR_FOUR_CORNERS','bounded explicit corner list required')
    pairs=[]
    for row in corners:
        if type(row) is not dict or set(row)!={'alpha_component','U_component'}:
            raise AppError('GRAMMAR_FOUR_CORNERS','corner pair must name alpha and U components')
        a,u=row['alpha_component'],row['U_component']
        if type(a) is not str or type(u) is not str or patch_targets.get(a)!='alpha' or patch_targets.get(u)!='U' or (a,u) in pairs:
            raise AppError('GRAMMAR_FOUR_CORNERS','unknown, duplicate or incorrectly typed corner pair')
        joint=tuple(x for x in ids if x in (a,u))
        if any(b not in blocks for b in ((),(a,),(u,),joint)):
            raise AppError('GRAMMAR_FOUR_CORNERS','all four corners must be independently admitted')
        pairs.append((a,u))
    return Grammar(m,patch_rows,patch_targets,tuple(blocks),region,selected,raw['horizon'],raw['value_type'],tuple(pairs),semantic_identity('finite-admissible-grammar',raw))


def apply_block(grammar:Grammar,block:tuple[str,...])->FiniteWorld:
    if block not in grammar.blocks:raise AppError('GRAMMAR_ADMISSION','unadmitted combination')
    raw=grammar.baseline.canonical_data()
    alpha={(row['s'],row['x']):row for row in raw['alpha']}
    U={(row['s'],row['x'],row['a'],row['xp']):row for row in raw['U']}
    for name in block:
        for key,vals in grammar.patch_rows[name].items():
            target,indices=key[0],key[1:]
            row=alpha[indices] if target=='alpha' else U[indices]
            outputs=grammar.baseline.actions if target=='alpha' else grammar.baseline.strategic
            row['weights']={a:v for a,v in zip(outputs,vals)}
    treated=parse_finite_world(raw)
    target_types={grammar.patch_targets[name] for name in block}
    if target_types:
        compare_strategic_intervention(grammar.baseline,treated,'alpha+U' if len(target_types)==2 else target_types.pop())
    return treated


def finite_block_value(K,region,starts,h,typ):
    n=len(K);region=set(region)
    vals=[Fraction(int(i in region)) for i in range(n)]
    for _ in range(h):
        vals=[sum((K[i][j]*vals[j] for j in region),Fraction(0)) if i in region else Fraction(0) for i in range(n)]
        if any(max(q.numerator.bit_length(),q.denominator.bit_length())>8192 for q in vals):
            raise AppError('GRAMMAR_RESOURCE','exact rational exceeds budget')
    return tuple(vals[i] if typ=='survival_horizon' else 1-vals[i] for i in starts)


def propose_grammar(raw:object)->dict:
    g=parse_grammar(raw)
    perblock=[]
    baseline=finite_block_value(induced_kernel(g.baseline),g.region,g.comparison,g.horizon,g.value_type)
    for b in g.blocks:
        m=apply_block(g,b)
        vals=finite_block_value(induced_kernel(m),g.region,g.comparison,g.horizon,g.value_type)
        effects=tuple(v-ref for v,ref in zip(vals,baseline))
        perblock.append({'component_ids':list(b),'treated_identity':m.semantic_id(),
                         'values_by_comparison_state':[rational_text(v) for v in vals],
                         'effects_vs_baseline':[rational_text(v) for v in effects],
                         'positive_on_full_comparison_set':all(v>0 for v in effects)})
    positive={tuple(row['component_ids']) for row in perblock if row['positive_on_full_comparison_set']}
    minimal=[list(b) for b in g.blocks if b in positive and not any(set(other)<set(b) for other in positive)]
    corners=[]
    lookup={tuple(row['component_ids']):row for row in perblock}
    ids=list(g.patch_targets)
    for a,u in g.four_corners:
        joint=tuple(x for x in ids if x in (a,u))
        values=[tuple(exact_result(v) for v in lookup[key]['values_by_comparison_state'])
                for key in ((),(a,),(u,),joint)]
        interactions=[values[3][i]-values[1][i]-values[2][i]+values[0][i] for i in range(len(g.comparison))]
        corners.append({'alpha_component':a,'U_component':u,'joint_component_ids':list(joint),
                        'interactions_by_comparison_state':[rational_text(v) for v in interactions]})
    return {'format':RECEIPT,'request_identity':g.semantic_id,'baseline_identity':g.baseline.semantic_id(),
            'admitted_blocks':[list(b) for b in g.blocks],
            'region_indices':list(g.region),'comparison_indices':list(g.comparison),
            'horizon':g.horizon,'value_type':g.value_type,
            'baseline_values':[rational_text(v) for v in baseline],
            'block_results':perblock,'minimal_positive_blocks':minimal,'four_corners':corners,
            'admission_scope':'EXACT_DECLARED_BLOCKS_ONLY_NO_DOWNWARD_CLOSURE',
            'claim_scope':'FINITE_NUMERIC_EFFECT_NOT_CONSTITUTIVE_CERTIFICATION',
            'P_held_fixed':True,'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
            'scientific_claims_verified':False}
