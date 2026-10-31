"""Independent exact checker for finite two-player protocol receipts.

Does not import the producer. Re-reads the canonical tables, checks every row
is stochastic, rebuilds the three joint kernels by expanding joint actions in
the opposite loop order, and requires the receipt to match exactly. It is not
a Lean proof or an independent certification.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import canonical_bytes, semantic_identity, rational_text

REQUEST = 'Permansson.App.FiniteMultiAgentRequest.v1'
RECEIPT = 'Permansson.App.FiniteMultiAgentReceipt.v1'


def _fail(msg):
    raise AppError('MULTIAGENT_RECEIPT', msg)


def _leaf(row, width):
    if type(row) is not list or len(row) != width:
        _fail('bad row width')
    vals = [exact_ratio(v, probability=True) for v in row]
    if sum(vals, Fraction(0)) != 1:
        _fail('row not stochastic')
    return vals


def _tab(raw, shape, width):
    if not shape:
        return _leaf(raw, width)
    if type(raw) is not list or len(raw) != shape[0]:
        _fail('bad table shape')
    return [_tab(x, shape[1:], width) for x in raw]


def _kernel(dims, act, upd, common, world):
    k0, k, nx, m = dims
    N = k0 * k * k * nx
    K = [[Fraction(0)] * N for _ in range(N)]
    for y in range(N):
        for a1 in range(m):
            for a0 in range(m):
                ai = a0 * m + a1
                pa = act[0][y][a0] * act[1][y][a1]
                for x2 in range(nx):
                    px = pa * world[y][ai][x2]
                    for c2 in range(k0):
                        for p0 in range(k):
                            for p1 in range(k):
                                z = ((c2 * k + p0) * k + p1) * nx + x2
                                K[y][z] += (px * common[y][ai][x2][c2] * upd[0][y][ai][x2][p0]
                                            * upd[1][y][ai][x2][p1])
    return K


def check_multiagent(raw: object, receipt: object) -> dict:
    if type(raw) is not dict or raw.get('format') != REQUEST or type(receipt) is not dict:
        _fail('unsupported request or receipt')
    lab = raw['labels']
    dims = tuple(len(lab[key]) for key in ('common', 'private', 'world', 'actions'))
    k0, k, nx, m = dims
    N, M = k0 * k * k * nx, m * m
    if any(not 1 <= d <= 2 for d in dims):
        _fail('dimension out of scope')

    def player(item):
        return _tab(item['action'], [N], m), _tab(item['update'], [N, M, nx], k)

    ps = [player(p) for p in raw['players']]
    common = _tab(raw['common_update'], [N, M, nx], k0)
    world = _tab(raw['world'], [N, M], nx)
    i = raw['treated_player']
    repl = player(raw['replacement'])
    anchors = [player(a) for a in raw['anchor']]
    profiles = {'baseline_kernel': ps,
                'closed_loop_kernel': [repl if j == i else ps[j] for j in range(2)],
                'open_loop_kernel': [repl if j == i else anchors[j] for j in range(2)]}
    kernels = {}
    for key, players in profiles.items():
        K = _kernel(dims, [p[0] for p in players], [p[1] for p in players], common, world)
        if any(sum(row, Fraction(0)) != 1 for row in K):
            _fail('joint kernel not stochastic')
        if receipt.get(key) != [[rational_text(v) for v in row] for row in K]:
            _fail(key + ' differs from the independent expansion')
        kernels[key] = K
    tv = [sum((abs(a - b) for a, b in zip(rc, ro)), Fraction(0)) / 2
          for rc, ro in zip(kernels['closed_loop_kernel'], kernels['open_loop_kernel'])]
    expected = {'closed_open_row_tv': [rational_text(v) for v in tv],
                'closed_open_max_tv': rational_text(max(tv)), 'treated_player': i,
                'physical_P_changed': False,
                'dimensions': {'common': k0, 'private': k, 'world': nx, 'actions': m},
                'request_identity': semantic_identity('finite-two-player-protocol', raw),
                'format': RECEIPT, 'lean_status': 'NOT_EXECUTED',
                'empirical_identification': 'NOT_IDENTIFIED', 'scientific_claims_verified': False,
                'scope_status': 'SYMMETRIC_TWO_PLAYER_PRODUCT_ACTIONS_EXACT_FINITE'}
    for key, value in expected.items():
        if receipt.get(key) != value:
            _fail(key + ' mismatch')
    if set(receipt) != set(expected) | set(profiles) | {'joint_states'} or \
            type(receipt['joint_states']) is not list or len(receipt['joint_states']) != N:
        _fail('receipt fields mismatch')
    return {'format': 'Permansson.App.IndependentMultiAgentCheck.v1', 'status': 'PASS',
            'joint_states': N, 'kernels_checked': 3,
            'receipt_sha256': sha256(canonical_bytes(receipt)).hexdigest(),
            'lean_status': 'NOT_EXECUTED', 'scientific_claims_verified': False}
