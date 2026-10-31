"""Exact transport of a finite CQ-1 certificate to an approximate model pair.

The request carries a CQ-1 request (the certified baseline and strategic
intervention) and an approximate baseline and treated model. Both share the
certified baseline's states, feasible actions and P, and differ from each
other by the same declared intervention target. The one-step budgets are the
exact maxima of the row total variation (half L1) between the certified and
approximate induced kernels, `δ₀` for the baselines and `δJ` for the treated
models. Research's transport theorem then gives the approximate pair a finite
constitutive certificate. Its persistence error is `min(1, η + e₀)` and its
margin `κ - e₀ - eJ`, where `e = 1 - (1 - δ)^L`, provided that margin is
positive. The approximate pair's own exact values are also computed, as a
consistency check the bound must respect; they are not used for the
transported certificate. The budgets are exact distances between declared
models, not empirical error estimates. Exact GR/PR and QSD are not claimed.
"""
from __future__ import annotations
from fractions import Fraction
from ..errors import AppError
from ..finite_world import parse_finite_world, compare_strategic_intervention, induced_kernel
from ..identity import semantic_identity, rational_text
from .cq1 import killed_survival, parse_cq1, propose_cq1

REQUEST = 'Permansson.App.CQ1TransportRequest.v1'
RECEIPT = 'Permansson.App.CQ1TransportReceipt.v1'


def parse_transport(raw: object):
    if type(raw) is not dict or set(raw) != {'format', 'cq1', 'approximate'} or raw['format'] != REQUEST:
        raise AppError('CQ1_TRANSPORT_INPUT', 'transport request requires exact versioned fields')
    approx = raw['approximate']
    if type(approx) is not dict or set(approx) != {'baseline', 'treated'}:
        raise AppError('CQ1_TRANSPORT_INPUT', 'approximate pair needs baseline and treated models')
    parsed = parse_cq1(raw['cq1'])
    base, check = parsed[0], parsed[2]
    a0, a1 = parse_finite_world(approx['baseline']), parse_finite_world(approx['treated'])
    for m in (a0, a1):
        if any(getattr(m, k) != getattr(base, k) for k in ('strategic', 'world', 'actions', 'feasible', 'P')):
            raise AppError('CQ1_TRANSPORT_INPUT', 'approximate models must share the states, feasible actions and P')
    compare_strategic_intervention(a0, a1, check['target'])
    return parsed, a0, a1


def row_tv(K, A):
    return [sum((abs(a - b) for a, b in zip(rk, ra)), Fraction(0)) / 2 for rk, ra in zip(K, A)]


def envelope(delta: Fraction, h: int) -> Fraction:
    return 1 - (1 - delta) ** h


def propose_cq1_transport(raw: object) -> dict:
    (base, treated, check, states, region, basin, comparison, prop, h, eta), a0, a1 = parse_transport(raw)
    cq1 = propose_cq1(raw['cq1'])
    if cq1['certificate_status'] != 'FINITE_CONSTITUTIVE_CERTIFICATE':
        raise AppError('CQ1_TRANSPORT_SCOPE', 'only a certified CQ-1 receipt can be transported')
    K0, K1, A0, A1 = (induced_kernel(m) for m in (base, treated, a0, a1))
    tv0, tvJ = row_tv(K0, A0), row_tv(K1, A1)
    d0, dJ = max(tv0), max(tvJ)
    e0, eJ = envelope(d0, h), envelope(dJ, h)
    kappa = Fraction(cq1['uniform_margin'])
    margin = kappa - e0 - eJ
    eta_t = min(Fraction(1), eta + e0)
    persist = killed_survival(A0, states, region, h)
    p0, p1 = killed_survival(A0, states, prop, h), killed_survival(A1, states, prop, h)
    direct_survival = min(persist[states.index(y)] for y in region)
    direct_margin = min(abs(p0[states.index(y)] - p1[states.index(y)]) for y in comparison)
    failed = [] if margin > 0 else ['BUDGET_ENVELOPES_EXCEED_MARGIN']
    if not failed and (direct_margin < margin or direct_survival < 1 - eta_t):
        raise AppError('CQ1_TRANSPORT_INTERNAL', 'direct approximate values violate the transported bound')
    return {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-cq1-transport', raw),
        'cq1_receipt': cq1,
        'approx_baseline_identity': a0.semantic_id(),
        'approx_treated_identity': a1.semantic_id(),
        'row_tv_baseline': [rational_text(v) for v in tv0],
        'row_tv_intervention': [rational_text(v) for v in tvJ],
        'delta_baseline': rational_text(d0),
        'delta_intervention': rational_text(dJ),
        'envelope_baseline': rational_text(e0),
        'envelope_intervention': rational_text(eJ),
        'transported_eta': rational_text(eta_t),
        'transported_margin': rational_text(margin),
        'transport_status': 'TRANSPORTED_FINITE_CONSTITUTIVE_CERTIFICATE' if not failed else 'NOT_TRANSPORTED',
        'failed_conditions': failed,
        'direct_approximate_check': {'min_region_survival': rational_text(direct_survival),
                                     'uniform_margin': rational_text(direct_margin)},
        'budget_semantics': 'EXACT_ROW_TV_BETWEEN_DECLARED_MODELS_NOT_EMPIRICAL_ERROR',
        'exact_GR_or_PR_certified': False,
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
