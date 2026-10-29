"""Independent arithmetic and admitted-family checker for finite patch grammars."""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import parse_finite_world,exact_ratio
from ..identity import canonical_bytes,rational_text
from ..engines.grammar import parse_grammar,RECEIPT

KEYS={'format','request_identity','baseline_identity','admitted_blocks',
      'region_indices','comparison_indices','horizon','value_type','baseline_values',
      'block_results','minimal_positive_blocks','four_corners','admission_scope',
      'claim_scope','P_held_fixed','lean_status','empirical_identification',
      'scientific_claims_verified'}


def reify_independent(g,block):
    # Independently reconstruct exact original-row changes rather than calling
    # engine.grammar.apply_block or the producer's induced-kernel evaluator.
    data=g.baseline.canonical_data()
    active={}
    for name in block:
        for key,weights in g.patch_rows[name].items():
            if key in active and active[key]!=weights:
                raise AppError('GRAMMAR_RECEIPT','incompatible patch overlap')
            active[key]=weights
    for row in data['alpha']:
        key=('alpha',row['s'],row['x'])
        if key in active:
            row['weights']={a:v for a,v in zip(g.baseline.actions,active[key])}
    for row in data['U']:
        key=('U',row['s'],row['x'],row['a'],row['xp'])
        if key in active:
            row['weights']={a:v for a,v in zip(g.baseline.strategic,active[key])}
    treated=parse_finite_world(data)
    if any(getattr(treated,k)!=getattr(g.baseline,k) for k in ('strategic','world','actions','feasible','P')):
        raise AppError('GRAMMAR_RECEIPT','structural P or feasibility changed')
    return treated


def direct_value(m,region,starts,h,typ):
    pairs=[(s,x) for s in m.strategic for x in m.world]
    n=len(pairs)
    K=[]
    for s,x in pairs:
        row=[]
        for sp,xp in pairs:
            score=Fraction(0)
            for a in m.feasible[s,x]:
                score+=m.alpha[s,x][m.actions.index(a)]*m.P[s,x,a][m.world.index(xp)]*m.U[s,x,a,xp][m.strategic.index(sp)]
            row.append(score)
        if sum(row,Fraction(0))!=1:raise AppError('GRAMMAR_RECEIPT','joint law nonstochastic')
        K.append(row)
    in_region=set(region)
    v=[Fraction(int(i in in_region)) for i in range(n)]
    for _ in range(h):
        v=[sum((K[i][j]*v[j] for j in in_region),Fraction(0)) if i in in_region else Fraction(0)
           for i in range(n)]
    return tuple(v[i] if typ=='survival_horizon' else 1-v[i] for i in starts)


def check_grammar(raw:object,receipt:object)->dict:
    g=parse_grammar(raw)
    if type(receipt) is not dict or set(receipt)!=KEYS or receipt['format']!=RECEIPT:
        raise AppError('GRAMMAR_RECEIPT','wrong exact receipt contract')
    fixed={'request_identity':g.semantic_id,'baseline_identity':g.baseline.semantic_id(),
           'admitted_blocks':[list(b) for b in g.blocks],
           'region_indices':list(g.region),'comparison_indices':list(g.comparison),
           'horizon':g.horizon,'value_type':g.value_type,
           'admission_scope':'EXACT_DECLARED_BLOCKS_ONLY_NO_DOWNWARD_CLOSURE',
           'claim_scope':'FINITE_NUMERIC_EFFECT_NOT_CONSTITUTIVE_CERTIFICATION',
           'P_held_fixed':True,'lean_status':'NOT_EXECUTED',
           'empirical_identification':'NOT_IDENTIFIED','scientific_claims_verified':False}
    for key,value in fixed.items():
        if type(value) is bool:
            if receipt[key] is not value:raise AppError('GRAMMAR_RECEIPT',key+' changed')
        elif canonical_bytes(receipt[key])!=canonical_bytes(value):raise AppError('GRAMMAR_RECEIPT',key+' mismatch')
    baseline=direct_value(g.baseline,g.region,g.comparison,g.horizon,g.value_type)
    if receipt['baseline_values']!=[rational_text(x) for x in baseline]:
        raise AppError('GRAMMAR_RECEIPT','baseline values wrong')
    rows=receipt['block_results']
    if type(rows) is not list or len(rows)!=len(g.blocks):
        raise AppError('GRAMMAR_RECEIPT','admitted block result missing')
    values={};positives=[]
    expected_fields={'component_ids','treated_identity','values_by_comparison_state','effects_vs_baseline','positive_on_full_comparison_set'}
    for row,block in zip(rows,g.blocks):
        if type(row) is not dict or set(row)!=expected_fields or row['component_ids']!=list(block):
            raise AppError('GRAMMAR_RECEIPT','foreign or reordered block')
        treat=reify_independent(g,block)
        if row['treated_identity']!=treat.semantic_id():
            raise AppError('GRAMMAR_RECEIPT','actual intervened model identity wrong')
        val=direct_value(treat,g.region,g.comparison,g.horizon,g.value_type)
        delta=tuple(v-b for v,b in zip(val,baseline))
        positive=all(d>0 for d in delta)
        if (row['values_by_comparison_state']!=[rational_text(x) for x in val] or
            row['effects_vs_baseline']!=[rational_text(x) for x in delta] or
            row['positive_on_full_comparison_set'] is not positive):
            raise AppError('GRAMMAR_RECEIPT','actual effect or full-comparison result wrong')
        values[block]=val
        if positive:positives.append(block)
    minimal=[list(b) for b in g.blocks if b in positives and not any(set(other)<set(b) for other in positives)]
    if receipt['minimal_positive_blocks']!=minimal:
        raise AppError('GRAMMAR_RECEIPT','incomplete or illegitimate minimal positive blocks')
    expected_corners=[]
    for a,u in g.four_corners:
        jointly=tuple(x for x in g.patch_targets if x in (a,u))
        cross=tuple(values[jointly][i]-values[(a,)][i]-values[(u,)][i]+values[()][i]
                    for i in range(len(g.comparison)))
        expected_corners.append({'alpha_component':a,'U_component':u,'joint_component_ids':list(jointly),
                                 'interactions_by_comparison_state':[rational_text(v) for v in cross]})
    if receipt['four_corners']!=expected_corners:
        raise AppError('GRAMMAR_RECEIPT','four-corner sequential effects wrong or unadmitted')
    return {'format':'Permansson.App.IndependentGrammarCheck.v1','status':'PASS',
            'checked_admitted_blocks':len(g.blocks),
            'checked_comparison_states':len(g.comparison),
            'receipt_sha256':sha256(canonical_bytes(receipt)).hexdigest(),
            'proof_status':'NOT_EXECUTED','claim_status':'FROZEN_GRAMMAR_NUMERIC_ONLY'}
