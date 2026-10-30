"""Exact adaptive admitted-block control over a finite patch grammar.

Before every α → P → U stage the controller selects one whole admitted block
(the baseline with exactly that block's α/U patch rows; P is never changed),
the block's induced joint row moves the state, and the full history may
select a different block next time: the timing of Research's
`AdaptiveGrammarControl`. The objective is the grammar's own: survival in the
region through the horizon, or exit from it by the horizon. A single flag,
"every observed state so far lies in the region", is the only memory the
objective needs, so the exact layer-wise Bellman table over (joint state,
flag) is the optimum over every history-dependent behavioral block
controller. The receipt reports the table, every tied optimal block per
remaining horizon and in-region state, each frozen block's value, the best
frozen block per start state and the adaptivity gain. Only declared blocks are
controls; downward closure and joint blocks that were not admitted are never
assumed.
"""
from __future__ import annotations
from fractions import Fraction
from ..errors import AppError
from ..finite_world import induced_kernel
from ..identity import rational_text, semantic_identity
from .grammar import apply_block, parse_grammar

REQUEST = 'Permansson.App.AdaptiveGrammarRequest.v1'
RECEIPT = 'Permansson.App.AdaptiveGrammarReceipt.v1'
MAX_BITS = 8192


def parse_adaptive(raw: object):
    if type(raw) is not dict or set(raw) != {'format', 'grammar'} or raw['format'] != REQUEST:
        raise AppError('ADAPTIVE_INPUT', 'adaptive request requires exact versioned fields')
    g = parse_grammar(raw['grammar'])
    if len(g.blocks) > 8 or g.horizon > 8:
        raise AppError('ADAPTIVE_SCOPE', 'at most 8 admitted blocks and 8 transitions')
    return g


def _table(kernels, region, horizon, survival):
    """table[r][y][flag] for r remaining transitions; flag = still inside."""
    n = len(kernels[0])
    table = [[[Fraction(int(f == survival)) for f in (False, True)] for _ in range(n)]]
    choices = []
    for _ in range(horizon):
        prev = table[-1]
        layer, chosen = [], []
        for y in range(n):
            cell = []
            for f in (False, True):
                scores = [sum((K[y][z] * prev[z][int(f and z in region)] for z in range(n)), Fraction(0))
                          for K in kernels]
                best = max(scores)
                if max(best.numerator.bit_length(), best.denominator.bit_length()) > MAX_BITS:
                    raise AppError('ADAPTIVE_RESOURCE', 'exact rational exceeds budget')
                cell.append(best)
                if f and y in region:
                    chosen.append([y, [i for i, v in enumerate(scores) if v == best]])
            layer.append(cell)
        table.append(layer)
        choices.append(chosen)
    return table, choices


def propose_adaptive(raw: object) -> dict:
    g = parse_adaptive(raw)
    survival = g.value_type == 'survival_horizon'
    region = set(g.region)
    kernels = [induced_kernel(apply_block(g, b)) for b in g.blocks]
    table, choices = _table(kernels, region, g.horizon, survival)
    H = g.horizon
    adaptive = [table[H][y][int(y in region)] for y in g.comparison]
    frozen = []
    for K in kernels:
        single, _ = _table([K], region, H, survival)
        frozen.append([single[H][y][int(y in region)] for y in g.comparison])
    best = [max(col) for col in zip(*frozen)]
    txt = lambda values: [rational_text(v) for v in values]
    return {
        'format': RECEIPT,
        'request_identity': semantic_identity('finite-adaptive-grammar', raw),
        'admitted_blocks': [list(b) for b in g.blocks],
        'region_indices': list(g.region),
        'start_indices': list(g.comparison),
        'horizon': H,
        'value_type': g.value_type,
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
