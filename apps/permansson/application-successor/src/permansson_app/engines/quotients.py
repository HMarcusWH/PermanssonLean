"""Exact finite, type-respecting quotient of the induced strategic-world Markov law.

The result checks every fiber under the baseline and *every declared* intervention.
It does NOT infer a quotient alpha/P/U decomposition, GR/PR status, approximate
bisimulation, or a causal identification result from the quotient kernel.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld, parse_finite_world, induced_kernel, compare_strategic_intervention, _TOKEN, _tokens
from ..identity import rational_text, semantic_identity

FORMAT = 'Permansson.App.FiniteTypedQuotientRequest.v1'
RECEIPT = 'Permansson.App.FiniteTypedQuotientReceipt.v1'
MAX_JOINT = 12
MAX_INTERVENTIONS = 8
MAX_HORIZON = 16
MAX_RESULT_BITS = 8192


@dataclass(frozen=True)
class Quotient:
    baseline: FiniteWorld
    interventions: tuple[tuple[str, str, FiniteWorld], ...]
    fine_states: tuple[tuple[str, str], ...]
    coarse_states: tuple[tuple[str, str], ...]
    coarse_index: tuple[int, ...]
    fibers: tuple[tuple[int, ...], ...]
    region: tuple[int, ...]
    coarse_region: tuple[int, ...]
    comparison: tuple[int, ...]
    coarse_comparison: tuple[int, ...]
    horizon: int
    value_type: str
    identity: dict


def parse_quotient(raw: object) -> Quotient:
    expected = {'format','baseline','interventions','quotient','region','comparison_states','horizon','value_type'}
    if type(raw) is not dict or set(raw) != expected or raw['format'] != FORMAT:
        raise AppError('QUOTIENT_INPUT', 'wrong typed quotient format or fields')
    m = parse_finite_world(raw['baseline'])
    fine = tuple((s,x) for s in m.strategic for x in m.world)
    if len(fine) > MAX_JOINT:
        raise AppError('QUOTIENT_SCOPE', 'at most 12 joint states supported')
    Q = raw['quotient']
    if type(Q) is not dict or set(Q) != {'strategic_states','world_states','strategic_map','world_map'}:
        raise AppError('QUOTIENT_MAP', 'type-respecting quotient maps required')
    CS = _tokens(Q['strategic_states'], 'quotient strategic states')
    CX = _tokens(Q['world_states'], 'quotient world states')
    coarse = tuple((s,x) for s in CS for x in CX)
    if type(Q['strategic_map']) is not dict or set(Q['strategic_map']) != set(m.strategic) or \
       type(Q['world_map']) is not dict or set(Q['world_map']) != set(m.world):
        raise AppError('QUOTIENT_MAP', 'exact source partition required for both types')
    if any(type(v) is not str or v not in CS for v in Q['strategic_map'].values()) or \
       any(type(v) is not str or v not in CX for v in Q['world_map'].values()):
        raise AppError('QUOTIENT_MAP', 'unknown coarse coordinate')
    if set(Q['strategic_map'].values()) != set(CS) or set(Q['world_map'].values()) != set(CX):
        raise AppError('QUOTIENT_MAP', 'maps must be onto both declared state types')
    projection = tuple(coarse.index((Q['strategic_map'][s], Q['world_map'][x])) for s,x in fine)
    if len(coarse) >= len(fine):
        raise AppError('QUOTIENT_SCOPE', 'identity or enlarged map is not a nontrivial quotient')
    fibers = tuple(tuple(i for i,v in enumerate(projection) if v == c) for c in range(len(coarse)))
    if any(not group for group in fibers):
        raise AppError('QUOTIENT_MAP','empty coarse fiber')

    def selected(key: str):
        given=raw[key]
        if type(given) is not list or not given or len(given)>len(fine):
            raise AppError('QUOTIENT_SET', f'{key}: nonempty finite state set required')
        indices=[]
        for pair in given:
            if type(pair) is not list or len(pair)!=2 or any(type(a) is not str for a in pair) or \
               tuple(pair) not in fine or fine.index(tuple(pair)) in indices:
                raise AppError('QUOTIENT_SET', f'{key}: repeated or foreign state')
            indices.append(fine.index(tuple(pair)))
        selected_set=set(indices)
        projected=set(projection[i] for i in indices)
        if selected_set != {i for i,c in enumerate(projection) if c in projected}:
            raise AppError('QUOTIENT_SET', f'{key}: must include every member of each selected fiber')
        return tuple(sorted(indices)), tuple(sorted(projected))

    region,coarse_region=selected('region')
    comparison,coarse_comparison=selected('comparison_states')
    if not set(comparison)<=set(region):
        raise AppError('QUOTIENT_SET','comparison must be within the declared regime region')
    if type(raw['horizon']) is not int or not (0 <= raw['horizon'] <= MAX_HORIZON) or \
       raw['value_type'] not in ('survival_horizon','exit_by_horizon'):
        raise AppError('QUOTIENT_SCOPE','only bounded exact survival/exit comparisons supported')
    specified=raw['interventions']
    if type(specified) is not list or not 1 <= len(specified) <= MAX_INTERVENTIONS:
        raise AppError('QUOTIENT_SCOPE','require 1..8 declared interventions')
    out=[]
    for item in specified:
        if type(item) is not dict or set(item) != {'id','target','model'}:
            raise AppError('QUOTIENT_INTERVENTION','typed intervention model required')
        tag=item['id'];target=item['target']
        if type(tag) is not str or not _TOKEN.fullmatch(tag) or tag=='baseline' or any(tag==x[0] for x in out):
            raise AppError('QUOTIENT_INTERVENTION','invalid or duplicate intervention ID')
        t=parse_finite_world(item['model'])
        compare_strategic_intervention(m,t,target)
        out.append((tag,target,t))
    return Quotient(m,tuple(out),fine,coarse,projection,fibers,region,coarse_region,
                    comparison,coarse_comparison,raw['horizon'],raw['value_type'],
                    semantic_identity('finite-typed-induced-quotient',raw))


def _bounded(values):
    if any(max(v.numerator.bit_length(),v.denominator.bit_length())>MAX_RESULT_BITS for v in values):
        raise AppError('QUOTIENT_RESOURCE','exact rational result exceeds bit budget')


def project_kernel(matrix, q: Quotient):
    """Check complete strong lumpability, not just one convenient representative."""
    result=[]
    for indices in q.fibers:
        row=tuple(sum((matrix[indices[0]][j] for j in target),Fraction(0)) for target in q.fibers)
        if sum(row,Fraction(0)) != 1: raise AppError('QUOTIENT_KERNEL','coarse row not stochastic')
        _bounded(row)
        for source in indices[1:]:
            other=tuple(sum((matrix[source][j] for j in target),Fraction(0)) for target in q.fibers)
            if other != row:
                raise AppError('QUOTIENT_LUMPABILITY','strong lumpability violated: source states in one fiber have different aggregate successors')
        result.append(row)
    return tuple(result)


def finite_event_values(matrix, region, start, horizon, value_type):
    n=len(matrix); B=set(region)
    v=[Fraction(int(i in B)) for i in range(n)]
    for _ in range(horizon):
        v=[sum((matrix[i][j]*v[j] for j in B),Fraction(0)) if i in B else Fraction(0)
           for i in range(n)]
        _bounded(v)
    return tuple((v[i] if value_type=='survival_horizon' else 1-v[i]) for i in start)


def propose_quotient(raw: object)->dict:
    q=parse_quotient(raw)
    profiles=[]
    for tag,target,model in [('baseline','baseline',q.baseline),*q.interventions]:
        fine=induced_kernel(model)
        coarse=project_kernel(fine,q)
        fv=finite_event_values(fine,q.region,q.comparison,q.horizon,q.value_type)
        cv=finite_event_values(coarse,q.coarse_region,q.coarse_comparison,q.horizon,q.value_type)
        if tuple(fv[i] for i,c in enumerate(q.comparison)) != tuple(cv[q.coarse_comparison.index(q.coarse_index[c])] for c in q.comparison):
            raise AppError('QUOTIENT_TRANSPORT','exact finite-event intertwining failed')
        profiles.append({'id':tag,'target':target,'source_identity':model.semantic_id(),
                         'coarse_kernel':[[rational_text(x) for x in row] for row in coarse],
                         'fine_values':[rational_text(v) for v in fv],
                         'coarse_values':[rational_text(v) for v in cv]})
    base_f=tuple(Fraction(s) for s in profiles[0]['fine_values'])
    base_c=tuple(Fraction(s) for s in profiles[0]['coarse_values'])
    effects=[{'id':p['id'],'fine_differences':[rational_text(Fraction(s)-b) for s,b in zip(p['fine_values'],base_f)],
              'coarse_differences':[rational_text(Fraction(s)-b) for s,b in zip(p['coarse_values'],base_c)]}
             for p in profiles[1:]]
    return {'format':RECEIPT,'request_identity':q.identity,'baseline_identity':q.baseline.semantic_id(),
            'fine_state_order':[list(p) for p in q.fine_states],
            'coarse_state_order':[list(p) for p in q.coarse_states],
            'fine_to_coarse_indices':list(q.coarse_index),
            'region_fine_indices':list(q.region),'region_coarse_indices':list(q.coarse_region),
            'comparison_fine_indices':list(q.comparison),'comparison_coarse_indices':list(q.coarse_comparison),
            'horizon':q.horizon,'value_type':q.value_type,'profiles':profiles,'effects':effects,
            'verified_law_scope':'TYPE_RESPECTING_INDUCED_MARKOV_QUOTIENT_NOT_COARSE_ALPHA_P_U',
            'comparison_scope':'FULL_FIBERS_ALL_DECLARED_INTERVENTIONS',
            'claim_scope':'FINITE_NUMERIC_TRANSPORT_ONLY_NOT_EXACT_GR_PR',
            'lean_status':'NOT_EXECUTED','empirical_identification':'NOT_IDENTIFIED',
            'scientific_claims_verified':False}
