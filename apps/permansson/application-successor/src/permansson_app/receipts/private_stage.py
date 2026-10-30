"""Independent exact checker for one-stage private-control saddle receipts.

Does not import the producer. Re-reads the payoff table, checks that both
declared mixtures are rational simplex vectors, that the controller mixture
earns at least the declared value against every nature parameter and that the
nature mixture holds every pure control to at most it - which together prove
the value is the greatest private value without any minimax theorem - and
recomputes the pure-control value. It is not a Lean proof or an independent
certification.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes, semantic_identity, rational_text

REQUEST = 'Permansson.App.PrivateStageRequest.v1'
RECEIPT = 'Permansson.App.PrivateStageReceipt.v1'


def _fail(msg):
    raise AppError('PRIVATE_STAGE_RECEIPT', msg)


def _simplex(raw, n, label):
    if type(raw) is not list or len(raw) != n:
        _fail(label + ' has wrong length')
    vals = [exact_ratio(v, probability=True) for v in raw]
    if sum(vals, Fraction(0)) != 1:
        _fail(label + ' is not a probability vector')
    return vals


def check_private_stage(raw: object, receipt: object) -> dict:
    if type(raw) is not dict or raw.get('format') != REQUEST or type(receipt) is not dict:
        _fail('unsupported request or receipt')
    controls, nature = raw['labels']['controls'], raw['labels']['nature']
    nc, nt = len(controls), len(nature)
    if not (1 <= nc <= 4 and 1 <= nt <= 4):
        _fail('dimension out of scope')
    Q = [[exact_ratio(v) for v in row] for row in raw['payoff']]
    if len(Q) != nt or any(len(row) != nc for row in Q):
        _fail('payoff table shape')
    p = _simplex(receipt.get('controller_mixture'), nc, 'controller mixture')
    q = _simplex(receipt.get('nature_mixture'), nt, 'nature mixture')
    if type(receipt.get('value')) is not str:
        _fail('value missing')
    v = exact_ratio(receipt['value'])
    # Column sums by nature parameter, then row sums by control: the opposite loop order.
    guarantee = [Fraction(0)] * nt
    hold = [Fraction(0)] * nc
    for c in range(nc):
        for t in range(nt):
            guarantee[t] += p[c] * Q[t][c]
            hold[c] += q[t] * Q[t][c]
    if any(g < v for g in guarantee):
        _fail('controller mixture does not guarantee the value')
    if any(h > v for h in hold):
        _fail('nature mixture does not hold every pure control to the value')
    worst = [Q[0][c] for c in range(nc)]
    for t in range(1, nt):
        worst = [min(a, Q[t][c]) for c, a in enumerate(worst)]
    r = max(worst)
    expected = {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-private-control-stage', raw),
        'controls': list(controls), 'nature': list(nature),
        'controller_guarantee_by_nature': [rational_text(x) for x in guarantee],
        'nature_hold_by_control': [rational_text(x) for x in hold],
        'pure_control_worst': [rational_text(x) for x in worst],
        'pure_control_value': rational_text(r),
        'pure_maxmin_controls': [controls[c] for c in range(nc) if worst[c] == r],
        'randomization_gain': rational_text(v - r),
        'timing': 'NATURE_SEES_MIXTURE_NOT_REALIZED_CONTROL',
        'scope_status': 'ONE_STAGE_PRIVATE_CONTROL_EXACT_FINITE',
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
    for key, value in expected.items():
        if receipt.get(key) != value:
            _fail(key + ' mismatch')
    if set(receipt) != set(expected) | {'value', 'controller_mixture', 'nature_mixture'} or \
            receipt['value'] != rational_text(v) or \
            receipt['controller_mixture'] != [rational_text(x) for x in p] or \
            receipt['nature_mixture'] != [rational_text(x) for x in q]:
        _fail('receipt fields mismatch')
    return {'format': 'Permansson.App.IndependentPrivateStageCheck.v1', 'status': 'PASS',
            'saddle_certificate': 'BOTH_SIDES_CHECKED', 'value': rational_text(v),
            'receipt_sha256': sha256(canonical_bytes(receipt)).hexdigest(),
            'lean_status': 'NOT_EXECUTED', 'scientific_claims_verified': False}
