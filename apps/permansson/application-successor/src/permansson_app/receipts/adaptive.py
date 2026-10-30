"""Independent exact checker for adaptive admitted-block control receipts.

Does not import the adaptive producer or the grammar engine's block
application. Every admitted block is rebuilt from the original rows with the
grammar checker's independent reifier, its joint kernel is summed directly
from α, P and U, and the Bellman table, all tied optimal blocks, every frozen
block value (by the plain region recursion, without the flag) and the
adaptivity gain are recomputed. It is not a Lean proof or an independent
certification.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..identity import canonical_bytes, semantic_identity, rational_text
from ..engines.grammar import parse_grammar
from .grammar import reify_independent

REQUEST = 'Permansson.App.AdaptiveGrammarRequest.v1'
RECEIPT = 'Permansson.App.AdaptiveGrammarReceipt.v1'


def _fail(msg):
    raise AppError('ADAPTIVE_RECEIPT', msg)


def _kernel(m):
    pairs = [(s, x) for s in m.strategic for x in m.world]
    K = []
    for s, x in pairs:
        row = [Fraction(0)] * len(pairs)
        for a in m.feasible[s, x]:
            pa = m.alpha[s, x][m.actions.index(a)]
            for j, (sp, xp) in enumerate(pairs):
                row[j] += pa * m.P[s, x, a][m.world.index(xp)] * m.U[s, x, a, xp][m.strategic.index(sp)]
        if sum(row, Fraction(0)) != 1:
            _fail('joint law nonstochastic')
        K.append(row)
    return K


def _frozen(K, region, starts, h, survival):
    v = [Fraction(int(i in region)) for i in range(len(K))]
    for _ in range(h):
        v = [sum((K[i][j] * v[j] for j in region), Fraction(0)) if i in region else Fraction(0)
             for i in range(len(K))]
    return [v[i] if survival else 1 - v[i] for i in starts]


def check_adaptive(raw: object, receipt: object) -> dict:
    if type(raw) is not dict or raw.get('format') != REQUEST or type(receipt) is not dict:
        _fail('unsupported request or receipt')
    g = parse_grammar(raw.get('grammar'))
    if len(g.blocks) > 8 or g.horizon > 8:
        _fail('scope')
    survival = g.value_type == 'survival_horizon'
    region, H = set(g.region), g.horizon
    kernels = [_kernel(reify_independent(g, b)) for b in g.blocks]
    n = len(kernels[0])
    # table[r][y] = [value with the flag False, value with the flag True]
    table = [[[Fraction(int(not survival)), Fraction(int(survival))] for _ in range(n)]]
    choices = []
    for _ in range(H):
        prev = table[-1]
        layer = [[None, None] for _ in range(n)]
        chosen = []
        for y in range(n):
            for flag in (True, False):
                scores = []
                for K in kernels:
                    total = Fraction(0)
                    for z in range(n):
                        total += K[y][z] * prev[z][1 if (flag and z in region) else 0]
                    scores.append(total)
                top = max(scores)
                layer[y][1 if flag else 0] = top
                if flag and y in region:
                    chosen.append([y, [i for i, v in enumerate(scores) if v == top]])
        table.append(layer)
        choices.append(chosen)
    adaptive = [table[H][y][1 if y in region else 0] for y in g.comparison]
    frozen = [_frozen(K, region, g.comparison, H, survival) for K in kernels]
    if any(a < f for row in frozen for a, f in zip(adaptive, row)):
        _fail('a frozen block beats the adaptive optimum')
    best = [max(col) for col in zip(*frozen)]
    txt = lambda values: [rational_text(v) for v in values]
    expected = {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-adaptive-grammar', raw),
        'admitted_blocks': [list(b) for b in g.blocks],
        'region_indices': list(g.region), 'start_indices': list(g.comparison),
        'horizon': H, 'value_type': g.value_type,
        'monitor_table': [[txt(cell) for cell in layer] for layer in table],
        'optimal_blocks': choices,
        'adaptive_values': txt(adaptive),
        'frozen_block_values': [txt(row) for row in frozen],
        'best_frozen_values': txt(best),
        'adaptivity_gain': txt(a - b for a, b in zip(adaptive, best)),
        'timing': 'BLOCK_SELECTED_BEFORE_EACH_ALPHA_P_U_STAGE',
        'policy_class': 'FULL_HISTORY_BEHAVIORAL_OVER_DECLARED_BLOCKS',
        'admission_scope': 'EXACT_DECLARED_BLOCKS_ONLY_NO_DOWNWARD_CLOSURE',
        'P_held_fixed': True,
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
    for key, value in expected.items():
        if receipt.get(key) != value:
            _fail(key + ' mismatch')
    if set(receipt) != set(expected):
        _fail('receipt fields mismatch')
    return {'format': 'Permansson.App.IndependentAdaptiveGrammarCheck.v1', 'status': 'PASS',
            'blocks': len(g.blocks), 'horizon': H,
            'receipt_sha256': sha256(canonical_bytes(receipt)).hexdigest(),
            'lean_status': 'NOT_EXECUTED', 'scientific_claims_verified': False}
