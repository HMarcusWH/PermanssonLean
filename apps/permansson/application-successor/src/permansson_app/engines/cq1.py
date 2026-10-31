"""Exact finite CQ-1 constitutive certificate for a prefix-survival score.

For a finite rational baseline and one declared strategic (alpha and/or U)
intervention with P and feasibility held fixed, this computes at horizon L the
killed survival in the declared region B for EVERY state of B (the
region-wide finite persistence gate, not only the comparison set) and the
probability of staying in a declared property set Q at times 0..L under both
models at every comparison state of B1. A finite constitutive certificate is
reported only when min_B survival >= 1 - eta and the smallest comparison
effect is positive. Exact GR/PR, QSD and error-budget transport are not
claimed, and no Lean replay happens here.
"""
from __future__ import annotations
from fractions import Fraction
from ..errors import AppError
from ..finite_world import parse_finite_world, compare_strategic_intervention, induced_kernel, exact_ratio
from ..identity import semantic_identity, rational_text

REQUEST = 'Permansson.App.FiniteCQ1Request.v1'
RECEIPT = 'Permansson.App.FiniteCQ1Receipt.v1'
FIELDS = {'format', 'baseline', 'intervention', 'region', 'basin', 'comparison', 'property_set', 'horizon', 'eta'}
MAX_STATES = 12
MAX_HORIZON = 16
MAX_BITS = 8192


def _states(raw: object, states: tuple, label: str, *, minimum: int = 1) -> tuple:
    if type(raw) is not list or not minimum <= len(raw) <= len(states):
        raise AppError('CQ1_INPUT', f'{label} must list {minimum}..{len(states)} joint states')
    result = []
    for pair in raw:
        if (type(pair) is not list or len(pair) != 2 or any(type(v) is not str for v in pair)
                or tuple(pair) not in states or tuple(pair) in result):
            raise AppError('CQ1_INPUT', f'foreign or repeated {label} state')
        result.append(tuple(pair))
    return tuple(result)


def parse_cq1(raw: object):
    if type(raw) is not dict or set(raw) != FIELDS or raw['format'] != REQUEST:
        raise AppError('CQ1_INPUT', 'CQ-1 request requires exact versioned fields')
    base = parse_finite_world(raw['baseline'])
    states = tuple((s, x) for s in base.strategic for x in base.world)
    if len(states) > MAX_STATES:
        raise AppError('CQ1_SCOPE', f'supports up to {MAX_STATES} joint states')
    item = raw['intervention']
    if type(item) is not dict or set(item) != {'target', 'treated'}:
        raise AppError('CQ1_INPUT', 'intervention must specify target and treated')
    treated = parse_finite_world(item['treated'])
    check = compare_strategic_intervention(base, treated, item['target'])
    region = _states(raw['region'], states, 'region')
    basin = _states(raw['basin'], states, 'basin')
    # The core comparison set needs two starts with different path laws;
    # two distinct starting states always differ at time 0.
    comparison = _states(raw['comparison'], states, 'comparison', minimum=2)
    prop = _states(raw['property_set'], states, 'property_set')
    if not set(basin) <= set(region) or not set(comparison) <= set(basin):
        raise AppError('CQ1_INPUT', 'comparison must lie in basin and basin in region')
    h = raw['horizon']
    if type(h) is not int or not 0 <= h <= MAX_HORIZON:
        raise AppError('CQ1_SCOPE', f'supported horizon is 0..{MAX_HORIZON}')
    eta = exact_ratio(raw['eta'], probability=True)
    return base, treated, check, states, region, basin, comparison, prop, h, eta


def killed_survival(K, states: tuple, inside: tuple, h: int) -> tuple:
    """Probability of staying in `inside` at observation times 0..h, per start."""
    keep = set(inside)
    values = tuple(Fraction(int(s in keep)) for s in states)
    for _ in range(h):
        values = tuple(sum((K[i][j] * values[j] for j, t in enumerate(states) if t in keep), Fraction(0))
                       if s in keep else Fraction(0) for i, s in enumerate(states))
        for q in values:
            if max(q.numerator.bit_length(), q.denominator.bit_length()) > MAX_BITS:
                raise AppError('CQ1_RESOURCE', 'exact rational exceeds bound')
    return values


def propose_cq1(raw: object) -> dict:
    base, treated, check, states, region, basin, comparison, prop, h, eta = parse_cq1(raw)
    K0, K1 = induced_kernel(base), induced_kernel(treated)
    persist = killed_survival(K0, states, region, h)
    base_prop = killed_survival(K0, states, prop, h)
    treat_prop = killed_survival(K1, states, prop, h)
    region_rows = [{'state': list(y), 'survival': rational_text(persist[states.index(y)])} for y in region]
    min_survival = min(persist[states.index(y)] for y in region)
    effects = []
    for y in comparison:
        i = states.index(y)
        effects.append((y, base_prop[i], treat_prop[i], abs(base_prop[i] - treat_prop[i])))
    margin = min(e for *_, e in effects)
    failed = []
    if min_survival < 1 - eta:
        failed.append('REGION_PERSISTENCE_BELOW_1_MINUS_ETA')
    if margin <= 0:
        failed.append('ZERO_UNIFORM_MARGIN')
    return {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-cq1-certificate', raw),
        'baseline_identity': base.semantic_id(),
        'treated_identity': treated.semantic_id(),
        'intervention_target': check['target'],
        'held_fixed': check['held_fixed'],
        'region': [list(y) for y in region], 'basin': [list(y) for y in basin],
        'comparison': [list(y) for y in comparison], 'property_set': [list(y) for y in prop],
        'horizon': h, 'eta': rational_text(eta),
        'region_survival': region_rows,
        'min_region_survival': rational_text(min_survival),
        'persistence_gate': 'PASS' if min_survival >= 1 - eta else 'FAIL',
        'comparison_effects': [{'state': list(y), 'baseline_property': rational_text(b),
                                'intervened_property': rational_text(t), 'effect': rational_text(e)}
                               for y, b, t, e in effects],
        'uniform_margin': rational_text(margin),
        'margin_attained_at': [list(y) for y, *_, e in effects if e == margin],
        'certificate_status': 'FINITE_CONSTITUTIVE_CERTIFICATE' if not failed else 'NOT_CERTIFIED',
        'failed_conditions': failed,
        'property': 'PREFIX_SURVIVAL_IN_PROPERTY_SET_AT_TIMES_0_TO_HORIZON',
        'scope_status': 'EXACT_FINITE_MODEL_NO_ERROR_BUDGET_TRANSPORT',
        'exact_GR_or_PR_certified': False,
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
