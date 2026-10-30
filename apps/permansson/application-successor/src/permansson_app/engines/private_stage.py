"""Exact one-stage private-control robust value with a two-sided saddle certificate.

Nature chooses a finite parameter theta after seeing the controller's mixed
strategy p but before the private control draw; the payoff is Q(theta, c), of
any sign. The private value of p is min_theta sum_c p(c) Q(theta, c). This
profile computes the greatest private value v over all mixed controllers by
exhaustive exact vertex enumeration of the controller program, an optimal
rational controller mixture, and by the same enumeration of nature's program a
rational nature mixture q holding every pure control to at most v. The pair
(p, q) is a literal saddle certificate: the checker never assumes a minimax
theorem or LP duality. It also reports the best pure-control value
r = max_c min_theta Q(theta, c) - the value of pure controls under private
timing and of the different revealed-control experiment, in which nature
observes the realized control - and the randomization gain v - r.
Multi-stage private games, committed nature, learning and empirical
identification are not claimed.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import semantic_identity, rational_text
from .rational_linear import solve_unique

REQUEST = 'Permansson.App.PrivateStageRequest.v1'
RECEIPT = 'Permansson.App.PrivateStageReceipt.v1'
MAX_LABELS = 4


def _labels(raw, key):
    values = raw.get(key) if type(raw) is dict else None
    if (type(values) is not list or not 1 <= len(values) <= MAX_LABELS or len(set(values)) != len(values)
            or any(type(v) is not str or not v for v in values)):
        raise AppError('PRIVATE_STAGE_SCOPE', f'{key} labels: 1..{MAX_LABELS} distinct strings')
    return list(values)


def parse_private_stage(raw: object):
    if type(raw) is not dict or set(raw) != {'format', 'labels', 'payoff'} or raw['format'] != REQUEST:
        raise AppError('PRIVATE_STAGE_INPUT', 'private-stage request requires exact versioned fields')
    if type(raw['labels']) is not dict or set(raw['labels']) != {'controls', 'nature'}:
        raise AppError('PRIVATE_STAGE_INPUT', 'labels need controls and nature')
    controls, nature = _labels(raw['labels'], 'controls'), _labels(raw['labels'], 'nature')
    table = raw['payoff']
    if type(table) is not list or len(table) != len(nature) or \
            any(type(row) is not list or len(row) != len(controls) for row in table):
        raise AppError('PRIVATE_STAGE_INPUT', 'payoff is one row per nature parameter, one entry per control')
    Q = [[exact_ratio(v) for v in row] for row in table]
    return controls, nature, Q


def _best_vertex(n, rows, sign):
    """Optimize the last coordinate of x = (w_0..w_{n-1}, z) over the simplex in w
    with `sign * (z - rows[k] . w) <= 0` for every k: sign 1 maximizes the
    guaranteed minimum, sign -1 minimizes the held maximum. Every candidate
    vertex makes n of the n + len(rows) inequalities tight beside sum w = 1."""
    best = None
    for tight in combinations(range(n + len(rows)), n):
        matrix, right = [[Fraction(1)] * n + [Fraction(0)]], [Fraction(1)]
        for t in tight:
            if t < n:
                matrix.append([Fraction(int(j == t)) for j in range(n)] + [Fraction(0)])
            else:
                matrix.append([-v for v in rows[t - n]] + [Fraction(1)])
            right.append(Fraction(0))
        try:
            x = solve_unique(matrix, right)
        except AppError as exc:
            if exc.code != 'LINEAR_SINGULAR':
                raise
            continue
        w, z = list(x[:n]), x[n]
        if any(v < 0 for v in w) or any(sign * (z - sum(a * b for a, b in zip(row, w))) > 0 for row in rows):
            continue
        if best is None or sign * (z - best[1]) > 0:
            best = (w, z)
    if best is None:
        raise AppError('PRIVATE_STAGE_INTERNAL', 'no feasible vertex')
    return best


def propose_private_stage(raw: object) -> dict:
    controls, nature, Q = parse_private_stage(raw)
    nc, nt = len(controls), len(nature)
    p, v = _best_vertex(nc, Q, 1)
    q, w = _best_vertex(nt, [[Q[t][c] for t in range(nt)] for c in range(nc)], -1)
    if v != w:
        raise AppError('PRIVATE_STAGE_INTERNAL', 'controller and nature programs disagree')
    guarantee = [sum((p[c] * Q[t][c] for c in range(nc)), Fraction(0)) for t in range(nt)]
    hold = [sum((q[t] * Q[t][c] for t in range(nt)), Fraction(0)) for c in range(nc)]
    pure = [min(Q[t][c] for t in range(nt)) for c in range(nc)]
    r = max(pure)
    return {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-private-control-stage', raw),
        'controls': controls,
        'nature': nature,
        'value': rational_text(v),
        'controller_mixture': [rational_text(x) for x in p],
        'nature_mixture': [rational_text(x) for x in q],
        'controller_guarantee_by_nature': [rational_text(x) for x in guarantee],
        'nature_hold_by_control': [rational_text(x) for x in hold],
        'pure_control_worst': [rational_text(x) for x in pure],
        'pure_control_value': rational_text(r),
        'pure_maxmin_controls': [controls[c] for c in range(nc) if pure[c] == r],
        'randomization_gain': rational_text(v - r),
        'timing': 'NATURE_SEES_MIXTURE_NOT_REALIZED_CONTROL',
        'scope_status': 'ONE_STAGE_PRIVATE_CONTROL_EXACT_FINITE',
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
