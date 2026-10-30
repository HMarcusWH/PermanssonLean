"""Independent exact checker for finite metric contraction receipts.

Does not import the producer. Rebuilds both joint kernels from direct
alpha/P/U events and the metric from the request, then validates every
transport certificate (coupling marginals, cost equal to the stated distance,
1-Lipschitz potential attaining it), the contraction factor and defect as the
exact maxima, both invariant laws (stochastic, invariant, unique) and the A3
bound. Optimal couplings are not unique, so certificates are validated rather
than recomputed. It is not a Lean proof or an independent certification.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import parse_finite_world, exact_ratio
from ..identity import canonical_bytes, semantic_identity, rational_text

REQUEST = 'Permansson.App.FiniteMetricRequest.v1'
RECEIPT = 'Permansson.App.FiniteMetricReceipt.v1'
FIELDS = {'format', 'request_identity', 'baseline_identity', 'perturbed_identity', 'states', 'metric',
          'baseline_kernel', 'perturbed_kernel', 'row_pair_transport', 'contraction_factor',
          'contraction_attained_at', 'row_defects', 'defect', 'invariant_law', 'perturbed_invariant_law',
          'invariant_transport', 'contraction_status', 'invariant_bound', 'scope_status', 'lean_status',
          'empirical_identification', 'scientific_claims_verified'}


def _fail(message):
    raise AppError('METRIC_RECEIPT', message)


def _direct_kernel(model, states):
    rows = []
    for s, x in states:
        row = {t: Fraction(0) for t in states}
        for a in model.feasible[s, x]:
            pa = model.alpha[s, x][model.actions.index(a)]
            for xp, px in zip(model.world, model.P[s, x, a]):
                for sp, pu in zip(model.strategic, model.U[s, x, a, xp]):
                    row[sp, xp] += pa * px * pu
        rows.append(tuple(row[t] for t in states))
    return tuple(rows)


def _rat(text):
    if type(text) is not str:
        _fail('rational fields must be strings')
    return exact_ratio(text)


def _vector(raw, n):
    if type(raw) is not list or len(raw) != n:
        _fail('bad vector length')
    return tuple(_rat(v) for v in raw)


def _check_transport(cert, mu, nu, d):
    if type(cert) is not dict:
        _fail('transport certificate must be an object')
    n = len(mu)
    value = _rat(cert['w1'])
    C = cert['coupling']
    if type(C) is not list or len(C) != n:
        _fail('bad coupling')
    C = [_vector(row, n) for row in C]
    f = _vector(cert['potential'], n)
    if any(v < 0 for row in C for v in row):
        _fail('negative coupling mass')
    if any(sum(C[i]) != mu[i] for i in range(n)) or any(sum(C[i][j] for i in range(n)) != nu[j] for j in range(n)):
        _fail('coupling marginals differ from the transported laws')
    if sum((C[i][j] * d[i][j] for i in range(n) for j in range(n)), Fraction(0)) != value:
        _fail('coupling cost differs from the stated distance')
    if any(f[i] - f[j] > d[i][j] for i in range(n) for j in range(n)):
        _fail('potential is not 1-Lipschitz')
    if sum((f[i] * (mu[i] - nu[i]) for i in range(n)), Fraction(0)) != value:
        _fail('potential does not attain the stated distance')
    return value


def _invariant(K, pi):
    n = len(K)
    if any(v < 0 for v in pi) or sum(pi) != 1:
        _fail('invariant law is not a probability vector')
    if any(sum(pi[x] * K[x][z] for x in range(n)) != pi[z] for z in range(n)):
        _fail('stated law is not invariant')
    # Uniqueness: K - I restricted to the balance equations plus normalization has full rank.
    rows = [[K[x][z] - Fraction(int(x == z)) for x in range(n)] for z in range(n)] + [[Fraction(1)] * n]
    rank, m = 0, [list(r) for r in rows]
    for col in range(n):
        pivot = next((r for r in range(rank, len(m)) if m[r][col] != 0), None)
        if pivot is None:
            continue
        m[rank], m[pivot] = m[pivot], m[rank]
        for r in range(len(m)):
            if r != rank and m[r][col] != 0:
                factor = m[r][col] / m[rank][col]
                m[r] = [a - factor * b for a, b in zip(m[r], m[rank])]
        rank += 1
    if rank != n:
        _fail('invariant law is not unique')


def check_metric(raw: object, receipt: object) -> dict:
    if type(raw) is not dict or raw.get('format') != REQUEST or type(receipt) is not dict or set(receipt) != FIELDS:
        _fail('unsupported request or receipt fields')
    if (receipt['format'] != RECEIPT or receipt['lean_status'] != 'NOT_EXECUTED'
            or receipt['scientific_claims_verified'] is not False
            or receipt['empirical_identification'] != 'NOT_IDENTIFIED'
            or receipt['scope_status'] != 'FINITE_METRIC_EXACT_TRANSPORT_NOT_POLISH_MOMENT_EVIDENCE'):
        _fail('false scientific scope')
    base = parse_finite_world(raw['baseline'])
    pert = parse_finite_world(raw['perturbed'])
    states = tuple((s, x) for s in base.strategic for x in base.world)
    n = len(states)
    if receipt['request_identity'] != semantic_identity('finite-metric-contraction', raw) or \
            receipt['baseline_identity'] != base.semantic_id() or receipt['perturbed_identity'] != pert.semantic_id():
        _fail('identity mismatch')
    if receipt['states'] != [list(s) for s in states]:
        _fail('state order mismatch')
    d = [[Fraction(0)] * n for _ in range(n)]
    for row in raw['metric']:
        i, j = states.index(tuple(row['a'])), states.index(tuple(row['b']))
        d[i][j] = d[j][i] = exact_ratio(row['distance'])
    if receipt['metric'] != [[rational_text(v) for v in r] for r in d]:
        _fail('metric mismatch')
    K, Kt = _direct_kernel(base, states), _direct_kernel(pert, states)
    if receipt['baseline_kernel'] != [[rational_text(v) for v in r] for r in K] or \
            receipt['perturbed_kernel'] != [[rational_text(v) for v in r] for r in Kt]:
        _fail('kernel mismatch with direct alpha/P/U events')
    pairs = receipt['row_pair_transport']
    expected = [(x, y) for x in range(n) for y in range(x + 1, n)]
    if type(pairs) is not list or len(pairs) != len(expected):
        _fail('row-pair certificates must cover every pair once')
    ratios = []
    for cert, (x, y) in zip(pairs, expected):
        if cert.get('a') != list(states[x]) or cert.get('b') != list(states[y]) or set(cert) != {'a', 'b', 'w1', 'ratio', 'coupling', 'potential'}:
            _fail('row-pair certificate order mismatch')
        value = _check_transport(cert, K[x], K[y], d)
        ratio = value / d[x][y]
        if _rat(cert['ratio']) != ratio:
            _fail('stated ratio mismatch')
        ratios.append(((x, y), ratio))
    rho = max(r for _, r in ratios)
    if _rat(receipt['contraction_factor']) != rho or receipt['contraction_attained_at'] != \
            [[list(states[x]), list(states[y])] for (x, y), r in ratios if r == rho]:
        _fail('contraction factor is not the exact maximum')
    defects = receipt['row_defects']
    if type(defects) is not list or len(defects) != n:
        _fail('row defects must cover every state')
    values = []
    for y, cert in enumerate(defects):
        if cert.get('state') != list(states[y]) or set(cert) != {'state', 'w1', 'coupling', 'potential'}:
            _fail('row defect order mismatch')
        values.append(_check_transport(cert, K[y], Kt[y], d))
    delta = max(values)
    if _rat(receipt['defect']) != delta:
        _fail('defect is not the exact maximum')
    pi, pit = _vector(receipt['invariant_law'], n), _vector(receipt['perturbed_invariant_law'], n)
    _invariant(K, pi)
    _invariant(Kt, pit)
    w = _check_transport(receipt['invariant_transport'], pi, pit, d)
    if set(receipt['invariant_transport']) != {'w1', 'coupling', 'potential'}:
        _fail('invariant transport fields')
    contractive = rho < 1
    if receipt['contraction_status'] != ('STRICT_W1_CONTRACTION' if contractive else 'NOT_CONTRACTIVE'):
        _fail('contraction status mismatch')
    if contractive:
        bound = delta / (1 - rho)
        if receipt['invariant_bound'] != rational_text(bound) or w > bound:
            _fail('A3 bound mismatch')
    elif receipt['invariant_bound'] is not None:
        _fail('no bound may be reported without strict contraction')
    return {'format': 'Permansson.App.IndependentMetricCheck.v1', 'status': 'PASS',
            'transport_certificates_checked': len(pairs) + n + 1,
            'contraction_status': receipt['contraction_status'],
            'receipt_sha256': sha256(canonical_bytes(receipt)).hexdigest(),
            'lean_status': 'NOT_EXECUTED', 'scientific_claims_verified': False}
