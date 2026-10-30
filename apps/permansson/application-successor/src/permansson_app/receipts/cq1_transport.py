"""Independent exact checker for CQ-1 certificate transport receipts.

Does not import the transport producer. The embedded CQ-1 receipt goes
through the independent CQ-1 checker. Every induced kernel is summed directly
from α, P and U. The approximate models must share the certified baseline's
states, feasible actions and P, and must change only the declared target.
The checker recomputes the row total variation, budgets, envelopes, the
transported error and margin, and the approximate pair's own survival and
margin, which must respect the transported bound. It is not a Lean proof or
an independent certification.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import parse_finite_world
from ..identity import canonical_bytes, semantic_identity, rational_text
from .cq1 import check_cq1

REQUEST = 'Permansson.App.CQ1TransportRequest.v1'
RECEIPT = 'Permansson.App.CQ1TransportReceipt.v1'


def _fail(msg):
    raise AppError('CQ1_TRANSPORT_RECEIPT', msg)


def _kernel(m, pairs):
    K = []
    for s, x in pairs:
        row = []
        for sp, xp in pairs:
            row.append(sum((m.alpha[s, x][m.actions.index(a)] * m.P[s, x, a][m.world.index(xp)]
                            * m.U[s, x, a, xp][m.strategic.index(sp)] for a in m.feasible[s, x]), Fraction(0)))
        if sum(row, Fraction(0)) != 1:
            _fail('joint law nonstochastic')
        K.append(row)
    return K


def _stay(K, inside, h):
    v = [Fraction(int(i in inside)) for i in range(len(K))]
    for _ in range(h):
        v = [sum((K[i][j] * v[j] for j in inside), Fraction(0)) if i in inside else Fraction(0)
             for i in range(len(K))]
    return v


def check_cq1_transport(raw: object, receipt: object) -> dict:
    if (type(raw) is not dict or raw.get('format') != REQUEST or type(receipt) is not dict
            or set(raw) != {'format', 'cq1', 'approximate'}):
        _fail('unsupported request or receipt')
    cq1 = receipt.get('cq1_receipt')
    check_cq1(raw['cq1'], cq1)
    if cq1['certificate_status'] != 'FINITE_CONSTITUTIVE_CERTIFICATE':
        _fail('embedded CQ-1 receipt is not a certificate')
    base = parse_finite_world(raw['cq1']['baseline'])
    treated = parse_finite_world(raw['cq1']['intervention']['treated'])
    a0 = parse_finite_world(raw['approximate']['baseline'])
    a1 = parse_finite_world(raw['approximate']['treated'])
    for m in (a0, a1):
        if any(getattr(m, k) != getattr(base, k) for k in ('strategic', 'world', 'actions', 'feasible', 'P')):
            _fail('approximate model changes states, feasibility or P')
    target = cq1['intervention_target']
    if (target == 'alpha' and a0.U != a1.U) or (target == 'U' and a0.alpha != a1.alpha):
        _fail('approximate intervention changes an undeclared primitive')
    pairs = [(s, x) for s in base.strategic for x in base.world]
    K0, K1, A0, A1 = (_kernel(m, pairs) for m in (base, treated, a0, a1))
    tv0 = [sum((abs(p - q) for p, q in zip(r, s)), Fraction(0)) / 2 for r, s in zip(K0, A0)]
    tvJ = [sum((abs(p - q) for p, q in zip(r, s)), Fraction(0)) / 2 for r, s in zip(K1, A1)]
    h = cq1['horizon']
    d0, dJ = max(tv0), max(tvJ)
    e0, eJ = 1 - (1 - d0) ** h, 1 - (1 - dJ) ** h
    kappa, eta = Fraction(cq1['uniform_margin']), Fraction(cq1['eta'])
    margin = kappa - e0 - eJ
    eta_t = min(Fraction(1), eta + e0)
    index = {tuple(p): i for i, p in enumerate(pairs)}
    region = {index[tuple(y)] for y in cq1['region']}
    prop = {index[tuple(y)] for y in cq1['property_set']}
    comparison = [index[tuple(y)] for y in cq1['comparison']]
    persist = _stay(A0, region, h)
    p0, p1 = _stay(A0, prop, h), _stay(A1, prop, h)
    direct_survival = min(persist[i] for i in region)
    direct_margin = min(abs(p0[i] - p1[i]) for i in comparison)
    transported = margin > 0
    if transported and (direct_margin < margin or direct_survival < 1 - eta_t):
        _fail('the approximate pair violates the transported bound')
    expected = {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-cq1-transport', raw),
        'cq1_receipt': cq1,
        'approx_baseline_identity': a0.semantic_id(),
        'approx_treated_identity': a1.semantic_id(),
        'row_tv_baseline': [rational_text(v) for v in tv0],
        'row_tv_intervention': [rational_text(v) for v in tvJ],
        'delta_baseline': rational_text(d0), 'delta_intervention': rational_text(dJ),
        'envelope_baseline': rational_text(e0), 'envelope_intervention': rational_text(eJ),
        'transported_eta': rational_text(eta_t), 'transported_margin': rational_text(margin),
        'transport_status': 'TRANSPORTED_FINITE_CONSTITUTIVE_CERTIFICATE' if transported else 'NOT_TRANSPORTED',
        'failed_conditions': [] if transported else ['BUDGET_ENVELOPES_EXCEED_MARGIN'],
        'direct_approximate_check': {'min_region_survival': rational_text(direct_survival),
                                     'uniform_margin': rational_text(direct_margin)},
        'budget_semantics': 'EXACT_ROW_TV_BETWEEN_DECLARED_MODELS_NOT_EMPIRICAL_ERROR',
        'exact_GR_or_PR_certified': False,
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
    for key, value in expected.items():
        if receipt.get(key) != value:
            _fail(key + ' mismatch')
    if set(receipt) != set(expected):
        _fail('receipt fields mismatch')
    return {'format': 'Permansson.App.IndependentCQ1TransportCheck.v1', 'status': 'PASS',
            'transport_status': expected['transport_status'],
            'receipt_sha256': sha256(canonical_bytes(receipt)).hexdigest(),
            'lean_status': 'NOT_EXECUTED', 'scientific_claims_verified': False}
