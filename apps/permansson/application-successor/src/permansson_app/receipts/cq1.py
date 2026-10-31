"""Independent exact checker for finite CQ-1 certificate receipts.

Does not import the producer's survival recursion: it expands every one-step
alpha/P/U event from the typed input for both models, re-derives every region
and comparison value, the margin, its attaining states and the certificate
status, and requires the receipt to match exactly. It is not a Lean proof or
an independent scientific certification.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import parse_finite_world, compare_strategic_intervention, exact_ratio
from ..identity import canonical_bytes, semantic_identity, rational_text

REQUEST = 'Permansson.App.FiniteCQ1Request.v1'
RECEIPT = 'Permansson.App.FiniteCQ1Receipt.v1'


def _same(got, expected, name='receipt'):
    if type(got) is not type(expected):
        raise AppError('CQ1_RECEIPT', name + ' type mismatch')
    if type(expected) is dict:
        if set(got) != set(expected):
            raise AppError('CQ1_RECEIPT', name + ' key mismatch')
        for key in expected:
            _same(got[key], expected[key], name + '.' + key)
    elif type(expected) is list:
        if len(got) != len(expected):
            raise AppError('CQ1_RECEIPT', name + ' array length mismatch')
        for i, (g, e) in enumerate(zip(got, expected)):
            _same(g, e, f'{name}[{i}]')
    elif got != expected:
        raise AppError('CQ1_RECEIPT', name + ' value mismatch')


def _direct_stay(model, states, inside, h):
    keep = set(inside)
    values = {y: Fraction(int(y in keep)) for y in states}
    for _ in range(h):
        nxt = {}
        for s, x in states:
            if (s, x) not in keep:
                nxt[s, x] = Fraction(0)
                continue
            prob = Fraction(0)
            for a in model.feasible[s, x]:
                pa = model.alpha[s, x][model.actions.index(a)]
                for xp, px in zip(model.world, model.P[s, x, a]):
                    for sp, pu in zip(model.strategic, model.U[s, x, a, xp]):
                        if (sp, xp) in keep:
                            prob += pa * px * pu * values[sp, xp]
            if not 0 <= prob <= 1 or max(prob.numerator.bit_length(), prob.denominator.bit_length()) > 8192:
                raise AppError('CQ1_RECEIPT', 'direct survival outside bounded probability')
            nxt[s, x] = prob
        values = nxt
    return values


def _pairs(raw, states):
    if type(raw) is not list or any(type(p) is not list or len(p) != 2 or tuple(p) not in states for p in raw):
        raise AppError('CQ1_RECEIPT', 'foreign state list')
    out = [tuple(p) for p in raw]
    if len(set(out)) != len(out):
        raise AppError('CQ1_RECEIPT', 'repeated state')
    return out


def check_cq1(raw: object, receipt: object) -> dict:
    if type(raw) is not dict or type(receipt) is not dict or raw.get('format') != REQUEST:
        raise AppError('CQ1_RECEIPT', 'unsupported request/receipt')
    base = parse_finite_world(raw['baseline'])
    treated = parse_finite_world(raw['intervention']['treated'])
    check = compare_strategic_intervention(base, treated, raw['intervention']['target'])
    states = tuple((s, x) for s in base.strategic for x in base.world)
    region = _pairs(raw['region'], states)
    basin = _pairs(raw['basin'], states)
    comparison = _pairs(raw['comparison'], states)
    prop = _pairs(raw['property_set'], states)
    if not region or not basin or len(comparison) < 2 or not prop:
        raise AppError('CQ1_RECEIPT', 'empty region/basin/property or fewer than two comparison states')
    if not set(basin) <= set(region) or not set(comparison) <= set(basin):
        raise AppError('CQ1_RECEIPT', 'comparison must lie in basin and basin in region')
    h = raw['horizon']
    if type(h) is not int or not 0 <= h <= 16:
        raise AppError('CQ1_RECEIPT', 'bad horizon')
    eta = exact_ratio(raw['eta'], probability=True)
    persist = _direct_stay(base, states, region, h)
    base_prop = _direct_stay(base, states, prop, h)
    treat_prop = _direct_stay(treated, states, prop, h)
    low = min(persist[y] for y in region)
    effects = [(y, base_prop[y], treat_prop[y], abs(base_prop[y] - treat_prop[y])) for y in comparison]
    margin = min(e for *_, e in effects)
    failed = ([] if low >= 1 - eta else ['REGION_PERSISTENCE_BELOW_1_MINUS_ETA']) + \
             ([] if margin > 0 else ['ZERO_UNIFORM_MARGIN'])
    expected = {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-cq1-certificate', raw),
        'baseline_identity': base.semantic_id(), 'treated_identity': treated.semantic_id(),
        'intervention_target': check['target'], 'held_fixed': check['held_fixed'],
        'region': [list(y) for y in region], 'basin': [list(y) for y in basin],
        'comparison': [list(y) for y in comparison], 'property_set': [list(y) for y in prop],
        'horizon': h, 'eta': rational_text(eta),
        'region_survival': [{'state': list(y), 'survival': rational_text(persist[y])} for y in region],
        'min_region_survival': rational_text(low),
        'persistence_gate': 'PASS' if low >= 1 - eta else 'FAIL',
        'comparison_effects': [{'state': list(y), 'baseline_property': rational_text(b),
                                'intervened_property': rational_text(t), 'effect': rational_text(e)}
                               for y, b, t, e in effects],
        'uniform_margin': rational_text(margin),
        'margin_attained_at': [list(y) for y, *_, e in effects if e == margin],
        'certificate_status': 'FINITE_CONSTITUTIVE_CERTIFICATE' if not failed else 'NOT_CERTIFIED',
        'failed_conditions': failed,
        'property': 'PREFIX_SURVIVAL_IN_PROPERTY_SET_AT_TIMES_0_TO_HORIZON',
        'scope_status': 'EXACT_FINITE_MODEL_NO_ERROR_BUDGET_TRANSPORT',
        'exact_GR_or_PR_certified': False, 'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED', 'scientific_claims_verified': False,
    }
    _same(receipt, expected)
    return {'format': 'Permansson.App.IndependentCQ1Check.v1', 'status': 'PASS',
            'region_wide_persistence_checked': len(region),
            'comparison_states_checked': len(comparison),
            'certificate_status': expected['certificate_status'],
            'receipt_sha256': sha256(canonical_bytes(receipt)).hexdigest(),
            'lean_status': 'NOT_EXECUTED', 'scientific_claims_verified': False}
