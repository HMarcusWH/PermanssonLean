"""Exact finite two-player protocol assembly with closed- and open-loop protocols.

Both players share `k` private states and `m` actions; there are `k0` common
and `nx` world states. Joint states are enumerated lexicographically as
(common, private 0, private 1, world) and joint actions as (a0, a1). Each
player supplies an action row per joint state and a private-update row per
(joint state, joint action, next world); a common-update row and the
physical world row P complete the protocol. The joint kernel is

    K(y, (c', p0', p1', x')) = sum_a act0(y, a0) act1(y, a1) P(y, a)(x')
                               common(y, a, x')(c') upd0(y, a, x')(p0') upd1(y, a, x')(p1').

For a declared treated player `i` and replacement mechanism `r` the profile
also computes the closed-loop kernel (only player `i` replaced) and the
open-loop kernel (the declared anchor profile installed, then player `i`
replaced), and the per-state total variation between their rows. P is never
changed by a protocol. Asymmetric player types, mediated or correlated
actions, private clocks and empirical game identification are not claimed.
"""
from __future__ import annotations
from fractions import Fraction
from itertools import product
from ..errors import AppError
from ..finite_world import exact_ratio
from ..identity import semantic_identity, rational_text

REQUEST = 'Permansson.App.FiniteMultiAgentRequest.v1'
RECEIPT = 'Permansson.App.FiniteMultiAgentReceipt.v1'
FIELDS = {'format', 'labels', 'players', 'common_update', 'world', 'treated_player', 'replacement', 'anchor'}
MAX_DIM = 2


def _labels(raw):
    if type(raw) is not dict or set(raw) != {'common', 'private', 'world', 'actions'}:
        raise AppError('MULTIAGENT_INPUT', 'labels need common, private, world and actions')
    out = {}
    for key, values in raw.items():
        if (type(values) is not list or not 1 <= len(values) <= MAX_DIM or len(set(values)) != len(values)
                or any(type(v) is not str or not v for v in values)):
            raise AppError('MULTIAGENT_SCOPE', f'{key} labels: 1..{MAX_DIM} distinct strings')
        out[key] = list(values)
    return out


def _row(raw, n, label):
    if type(raw) is not list or len(raw) != n:
        raise AppError('MULTIAGENT_INPUT', f'{label} row has wrong length')
    row = [exact_ratio(v, probability=True) for v in raw]
    if sum(row, Fraction(0)) != 1:
        raise AppError('MULTIAGENT_INPUT', f'{label} row is not stochastic')
    return row


def _table(raw, shape, width, label):
    """Nested list of shape `shape` whose leaves are stochastic rows of `width`."""
    if not shape:
        return _row(raw, width, label)
    if type(raw) is not list or len(raw) != shape[0]:
        raise AppError('MULTIAGENT_INPUT', f'{label} table has wrong shape')
    return [_table(item, shape[1:], width, label) for item in raw]


def parse_multiagent(raw: object):
    if type(raw) is not dict or set(raw) != FIELDS or raw['format'] != REQUEST:
        raise AppError('MULTIAGENT_INPUT', 'multi-agent request requires exact versioned fields')
    lab = _labels(raw['labels'])
    k0, k, nx, m = (len(lab[key]) for key in ('common', 'private', 'world', 'actions'))
    N, M = k0 * k * k * nx, m * m

    def player(item, label):
        if type(item) is not dict or set(item) != {'action', 'update'}:
            raise AppError('MULTIAGENT_INPUT', f'{label} needs action and update tables')
        return (_table(item['action'], [N], m, label + ' action'),
                _table(item['update'], [N, M, nx], k, label + ' update'))

    players = raw['players']
    if type(players) is not list or len(players) != 2:
        raise AppError('MULTIAGENT_SCOPE', 'exactly two players')
    ps = [player(p, f'player {i}') for i, p in enumerate(players)]
    common = _table(raw['common_update'], [N, M, nx], k0, 'common update')
    world = _table(raw['world'], [N, M], nx, 'world')
    i = raw['treated_player']
    if i not in (0, 1) or type(i) is not int:
        raise AppError('MULTIAGENT_INPUT', 'treated player must be 0 or 1')
    repl = player(raw['replacement'], 'replacement')
    anchor = raw['anchor']
    if type(anchor) is not list or len(anchor) != 2:
        raise AppError('MULTIAGENT_INPUT', 'anchor profile needs both players')
    anchors = [player(a, f'anchor {j}') for j, a in enumerate(anchor)]
    return lab, (k0, k, nx, m), ps, common, world, i, repl, anchors


def joint_kernel(dims, ps, common, world):
    k0, k, nx, m = dims
    states = list(product(range(k0), range(k), range(k), range(nx)))
    actions = list(product(range(m), range(m)))
    K = []
    for y in range(len(states)):
        row = []
        for c2, p0, p1, x2 in states:
            total = Fraction(0)
            for ai, (a0, a1) in enumerate(actions):
                total += (ps[0][0][y][a0] * ps[1][0][y][a1] * world[y][ai][x2] * common[y][ai][x2][c2]
                          * ps[0][1][y][ai][x2][p0] * ps[1][1][y][ai][x2][p1])
            row.append(total)
        if sum(row, Fraction(0)) != 1:
            raise AppError('MULTIAGENT_INTERNAL', 'joint row not stochastic')
        K.append(row)
    return K


def propose_multiagent(raw: object) -> dict:
    lab, dims, ps, common, world, i, repl, anchors = parse_multiagent(raw)
    closed = [repl if j == i else ps[j] for j in range(2)]
    opened = [repl if j == i else anchors[j] for j in range(2)]
    K, Kc, Ko = (joint_kernel(dims, players, common, world) for players in (ps, closed, opened))
    k0, k, nx, m = dims
    names = [{'common': lab['common'][c], 'private': [lab['private'][p0], lab['private'][p1]],
              'world': lab['world'][x]}
             for c, p0, p1, x in product(range(k0), range(k), range(k), range(nx))]
    tv = [sum((abs(a - b) for a, b in zip(rc, ro)), Fraction(0)) / 2 for rc, ro in zip(Kc, Ko)]
    txt = lambda rows: [[rational_text(v) for v in row] for row in rows]
    return {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-two-player-protocol', raw),
        'dimensions': {'common': k0, 'private': k, 'world': nx, 'actions': m},
        'joint_states': names,
        'treated_player': i,
        'baseline_kernel': txt(K),
        'closed_loop_kernel': txt(Kc),
        'open_loop_kernel': txt(Ko),
        'closed_open_row_tv': [rational_text(v) for v in tv],
        'closed_open_max_tv': rational_text(max(tv)),
        'physical_P_changed': False,
        'scope_status': 'SYMMETRIC_TWO_PLAYER_PRODUCT_ACTIONS_EXACT_FINITE',
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
