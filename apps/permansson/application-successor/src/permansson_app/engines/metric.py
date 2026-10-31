"""Exact finite W1 contraction and invariant-law perturbation (metric profile).

For a baseline and a perturbed typed alpha/P/U model on the same joint states
and a declared finite metric d, this computes every row-pair Wasserstein-1
distance of the baseline joint kernel K with an optimal coupling and a
1-Lipschitz dual potential, the contraction factor
rho = max_{x != y} W1(K_x, K_y) / d(x, y), the row defects
delta_y = W1(K_y, Kt_y) with delta = max_y delta_y, the unique invariant laws
of K and Kt, and W1(pi, pi_t) with its certificate. Only when rho < 1 is the
A3 bound W1(pi, pi_t) <= delta / (1 - rho) reported. A coupling alone is an
upper bound; every reported distance also carries a dual potential attaining
it. No Polish-space moment argument, Lean replay or empirical identification
happens here.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import combinations
from ..errors import AppError
from ..finite_world import parse_finite_world, induced_kernel, exact_ratio
from ..identity import semantic_identity, rational_text
from .rational_linear import solve_unique

REQUEST = 'Permansson.App.FiniteMetricRequest.v1'
RECEIPT = 'Permansson.App.FiniteMetricReceipt.v1'
MAX_STATES = 4
MAX_BITS = 8192


def _pair(raw, states, label):
    if (type(raw) is not list or len(raw) != 2 or any(type(v) is not str for v in raw)
            or tuple(raw) not in states):
        raise AppError('METRIC_INPUT', f'foreign {label} state')
    return states.index(tuple(raw))


def parse_metric(raw: object):
    if type(raw) is not dict or set(raw) != {'format', 'baseline', 'perturbed', 'metric'} or raw['format'] != REQUEST:
        raise AppError('METRIC_INPUT', 'metric request requires exact versioned fields')
    base = parse_finite_world(raw['baseline'])
    pert = parse_finite_world(raw['perturbed'])
    if (base.strategic, base.world) != (pert.strategic, pert.world):
        raise AppError('METRIC_INPUT', 'perturbed model must share the joint state space')
    states = tuple((s, x) for s in base.strategic for x in base.world)
    n = len(states)
    if not 2 <= n <= MAX_STATES:
        raise AppError('METRIC_SCOPE', f'supports 2..{MAX_STATES} joint states')
    rows = raw['metric']
    if type(rows) is not list or len(rows) != n * (n - 1) // 2:
        raise AppError('METRIC_INPUT', 'metric must list every unordered pair of distinct states once')
    d = [[Fraction(0)] * n for _ in range(n)]
    seen = set()
    for row in rows:
        if type(row) is not dict or set(row) != {'a', 'b', 'distance'}:
            raise AppError('METRIC_INPUT', 'metric rows need a, b and distance')
        i, j = _pair(row['a'], states, 'metric'), _pair(row['b'], states, 'metric')
        key = (min(i, j), max(i, j))
        if i == j or key in seen:
            raise AppError('METRIC_INPUT', 'metric pairs must be distinct and unrepeated')
        seen.add(key)
        value = exact_ratio(row['distance'])
        if value <= 0:
            raise AppError('METRIC_INPUT', 'distinct states need positive distance')
        d[i][j] = d[j][i] = value
    for i in range(n):
        for j in range(n):
            for k in range(n):
                if d[i][k] > d[i][j] + d[j][k]:
                    raise AppError('METRIC_INPUT', 'metric violates the triangle inequality')
    return base, pert, states, tuple(tuple(r) for r in d)


def _check_bits(values):
    for q in values:
        if max(q.numerator.bit_length(), q.denominator.bit_length()) > MAX_BITS:
            raise AppError('METRIC_RESOURCE', 'exact rational exceeds bound')


def _dual(diff, d):
    """max sum_i f_i diff_i over f_0 = 0, f_i - f_j <= d_ij (vertex enumeration)."""
    n = len(diff)
    cons = [(i, j) for i in range(n) for j in range(n) if i != j]
    best = None
    for chosen in combinations(cons, n - 1):
        A = []
        b = []
        for i, j in chosen:
            row = [Fraction(0)] * (n - 1)
            if i:
                row[i - 1] += 1
            if j:
                row[j - 1] -= 1
            A.append(row)
            b.append(d[i][j])
        try:
            sol = solve_unique(A, b)
        except AppError:
            continue
        f = (Fraction(0),) + tuple(sol)
        if any(f[i] - f[j] > d[i][j] for i, j in cons):
            continue
        value = sum((fi * di for fi, di in zip(f, diff)), Fraction(0))
        if best is None or value > best[0]:
            best = (value, f)
    if best is None:
        raise AppError('METRIC_INTERNAL', 'no feasible dual vertex')
    return best


def _excess_plan(supply, demand, d):
    """Min-cost plan moving `supply` (dict i->mass) onto `demand` (dict j->mass)."""
    rows, cols = sorted(supply), sorted(demand)
    cells = [(i, j) for i in rows for j in cols]
    size = len(rows) + len(cols) - 1
    best = None
    for basis in combinations(cells, size):
        A, b = [], []
        for i in rows:
            A.append([Fraction(int(c[0] == i)) for c in basis]); b.append(supply[i])
        for j in cols[:-1]:
            A.append([Fraction(int(c[1] == j)) for c in basis]); b.append(demand[j])
        try:
            sol = solve_unique(A, b)
        except AppError:
            continue
        if any(v < 0 for v in sol):
            continue
        cost = sum((v * d[i][j] for v, (i, j) in zip(sol, basis)), Fraction(0))
        if best is None or cost < best[0]:
            best = (cost, dict(zip(basis, sol)))
    if best is None:
        raise AppError('METRIC_INTERNAL', 'no feasible transport basis')
    return best


def transport(mu, nu, d):
    """Exact W1 with an optimal coupling and a 1-Lipschitz potential attaining it."""
    n = len(mu)
    diff = tuple(m - v for m, v in zip(mu, nu))
    coupling = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        coupling[i][i] = min(mu[i], nu[i])
    supply = {i: diff[i] for i in range(n) if diff[i] > 0}
    demand = {j: -diff[j] for j in range(n) if diff[j] < 0}
    cost = Fraction(0)
    if supply:
        cost, plan = _excess_plan(supply, demand, d)
        for (i, j), v in plan.items():
            coupling[i][j] += v
    value, potential = _dual(diff, d)
    if value != cost:
        raise AppError('METRIC_INTERNAL', 'transport primal and dual values differ')
    _check_bits([value, *potential, *(v for r in coupling for v in r)])
    return value, tuple(tuple(r) for r in coupling), potential


def invariant_law(K):
    n = len(K)
    A = [[K[x][z] - Fraction(int(x == z)) for x in range(n)] for z in range(n - 1)]
    A.append([Fraction(1)] * n)
    try:
        return solve_unique(A, [Fraction(0)] * (n - 1) + [Fraction(1)])
    except AppError:
        raise AppError('METRIC_SCOPE', 'invariant law is not unique') from None


def _cert(value, coupling, potential):
    return {'w1': rational_text(value),
            'coupling': [[rational_text(v) for v in row] for row in coupling],
            'potential': [rational_text(v) for v in potential]}


def propose_metric(raw: object) -> dict:
    base, pert, states, d = parse_metric(raw)
    K, Kt = induced_kernel(base), induced_kernel(pert)
    n = len(states)
    pairs = []
    for x in range(n):
        for y in range(x + 1, n):
            value, coupling, potential = transport(K[x], K[y], d)
            pairs.append((x, y, value / d[x][y], value, coupling, potential))
    rho = max(p[2] for p in pairs)
    defects = [(y, *transport(K[y], Kt[y], d)) for y in range(n)]
    delta = max(v for _, v, _, _ in defects)
    pi, pit = invariant_law(K), invariant_law(Kt)
    w, coupling, potential = transport(pi, pit, d)
    contractive = rho < 1
    bound = delta / (1 - rho) if contractive else None
    if contractive and w > bound:
        raise AppError('METRIC_INTERNAL', 'invariant-law distance exceeds the A3 bound')
    return {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-metric-contraction', raw),
        'baseline_identity': base.semantic_id(), 'perturbed_identity': pert.semantic_id(),
        'states': [list(s) for s in states],
        'metric': [[rational_text(v) for v in row] for row in d],
        'baseline_kernel': [[rational_text(v) for v in row] for row in K],
        'perturbed_kernel': [[rational_text(v) for v in row] for row in Kt],
        'row_pair_transport': [dict(_cert(v, c, f), a=list(states[x]), b=list(states[y]),
                                    ratio=rational_text(r)) for x, y, r, v, c, f in pairs],
        'contraction_factor': rational_text(rho),
        'contraction_attained_at': [[list(states[x]), list(states[y])] for x, y, r, *_ in pairs if r == rho],
        'row_defects': [dict(_cert(v, c, f), state=list(states[y])) for y, v, c, f in defects],
        'defect': rational_text(delta),
        'invariant_law': [rational_text(v) for v in pi],
        'perturbed_invariant_law': [rational_text(v) for v in pit],
        'invariant_transport': _cert(w, coupling, potential),
        'contraction_status': 'STRICT_W1_CONTRACTION' if contractive else 'NOT_CONTRACTIVE',
        'invariant_bound': rational_text(bound) if contractive else None,
        'scope_status': 'FINITE_METRIC_EXACT_TRANSPORT_NOT_POLISH_MOMENT_EVIDENCE',
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
