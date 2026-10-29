"""Exact finite-horizon rectangular max-min versus committed-model evaluation.

Nature observes the realized controller action before selecting a physical P row.
Rectangular nature may reselect at every node; committed nature fixes one full
P model before the entire trajectory. The committed comparison is for the
*declared fixed Markov controller*, not an optimal committed-nature game.

This is a finite numerical analogue of the repository's chronological model
families, not a data-to-Lean theorem, empirical identification, or proof of
unrestricted private-information policies.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld, parse_finite_world, exact_ratio, _TOKEN
from ..identity import rational_text, semantic_identity

FORMAT = 'Permansson.App.FiniteNatureChronologyRequest.v1'
RECEIPT = 'Permansson.App.FiniteNatureChronologyReceipt.v1'
MAX_JOINT_STATES = 12
MAX_HORIZON = 12
MAX_NATURE_MODELS = 6
MAX_RESULT_BITS = 8192


@dataclass(frozen=True)
class NatureProblem:
    baseline: FiniteWorld
    nature_ids: tuple[str, ...]
    nature_worlds: tuple[FiniteWorld, ...]
    states: tuple[tuple[str, str], ...]
    policy: tuple[str, ...]
    rewards: tuple[Fraction, ...]
    starts: tuple[int, ...]
    horizon: int
    identity: dict


def parse_nature(raw: object) -> NatureProblem:
    if type(raw) is not dict or set(raw) != {
        'format', 'baseline', 'nature_models', 'fixed_policy',
        'horizon', 'terminal_rewards', 'comparison_states'
    } or raw['format'] != FORMAT:
        raise AppError('NATURE_INPUT', 'incorrect version or field inventory')
    baseline = parse_finite_world(raw['baseline'])
    states = tuple((s, x) for s in baseline.strategic for x in baseline.world)
    if len(states) > MAX_JOINT_STATES or type(raw['horizon']) is not int or not (0 <= raw['horizon'] <= MAX_HORIZON):
        raise AppError('NATURE_SCOPE', 'at most 12 joint states and 12 transitions')
    scenarios = raw['nature_models']
    if type(scenarios) is not list or not 1 <= len(scenarios) <= MAX_NATURE_MODELS:
        raise AppError('NATURE_SCOPE', 'require 1..6 nonempty complete physical nature models')
    names = []
    worlds = []
    for item in scenarios:
        if type(item) is not dict or set(item) != {'id', 'P'} or type(item['id']) is not str or not _TOKEN.fullmatch(item['id']) or item['id'] in names:
            raise AppError('NATURE_MODEL', 'model id must be distinct and well typed')
        raw_model = baseline.canonical_data()
        # Only the complete physical P table can differ between models.
        raw_model['P'] = item['P']
        physical = parse_finite_world(raw_model)
        for key in ('strategic', 'world', 'actions', 'feasible', 'alpha', 'U'):
            if getattr(physical, key) != getattr(baseline, key):
                raise AppError('NATURE_HELD_FIXED', key + ' changed')
        names.append(item['id'])
        worlds.append(physical)
    policy_rows = raw['fixed_policy']
    if type(policy_rows) is not list or len(policy_rows) != len(states):
        raise AppError('NATURE_POLICY', 'fixed controller needs one legal action per state')
    choices = {}
    for entry in policy_rows:
        if type(entry) is not dict or set(entry) != {'s', 'x', 'action'}:
            raise AppError('NATURE_POLICY', 'policy row malformed')
        state = (entry['s'], entry['x'])
        if state not in states or state in choices or type(entry['action']) is not str or entry['action'] not in baseline.feasible[state]:
            raise AppError('NATURE_POLICY', 'policy must be complete, distinct, and feasible')
        choices[state] = entry['action']
    policy = tuple(choices[state] for state in states)
    reward_rows = raw['terminal_rewards']
    if type(reward_rows) is not list or len(reward_rows) != len(states):
        raise AppError('NATURE_REWARD', 'reward must be assigned to every joint state')
    reward_map = {}
    for entry in reward_rows:
        if type(entry) is not dict or set(entry) != {'s', 'x', 'value'}:
            raise AppError('NATURE_REWARD', 'terminal reward row malformed')
        state = (entry['s'], entry['x'])
        if state not in states or state in reward_map:
            raise AppError('NATURE_REWARD', 'duplicate or foreign reward state')
        reward_map[state] = exact_ratio(entry['value'])
    starts = []
    if type(raw['comparison_states']) is not list or not 1 <= len(raw['comparison_states']) <= len(states):
        raise AppError('NATURE_COMPARISON', 'require nonempty full declared comparison subset')
    for row in raw['comparison_states']:
        if type(row) is not list or len(row) != 2 or any(type(v) is not str for v in row):
            raise AppError('NATURE_COMPARISON', 'comparison state must be [s,x]')
        state = tuple(row)
        if state not in states or states.index(state) in starts:
            raise AppError('NATURE_COMPARISON', 'comparison state unknown or duplicate')
        starts.append(states.index(state))
    return NatureProblem(baseline, tuple(names), tuple(worlds), states,
        policy, tuple(reward_map[state] for state in states), tuple(sorted(starts)),
        raw['horizon'], semantic_identity('finite-nature-chronology', raw))


def _row(model: FiniteWorld, s: str, x: str, a: str,
         states: tuple[tuple[str, str], ...]) -> tuple[Fraction, ...]:
    return tuple(model.P[s, x, a][model.world.index(xp)] *
                 model.U[s, x, a, xp][model.strategic.index(sp)]
                 for sp, xp in states)


def _checked(values: tuple[Fraction, ...]) -> tuple[Fraction, ...]:
    if any(max(v.numerator.bit_length(), v.denominator.bit_length()) > MAX_RESULT_BITS for v in values):
        raise AppError('NATURE_RESOURCE', 'exact value exceeds rational output budget')
    return values


def propose_nature(raw: object) -> dict:
    q = parse_nature(raw)
    base = q.rewards
    fixed_rect = [base]
    game_opt = [base]
    committed = [[base] for _ in q.nature_worlds]
    game_argmax = [[[] for _ in q.states]]
    game_argmin = [[{} for _ in q.states]]
    fixed_argmin = [[[] for _ in q.states]]
    for _ in range(1, q.horizon + 1):
        fixed_values, optimal_values, fixed_choices, argmax_rows, argmin_rows = [], [], [], [], []
        for i, (s, x) in enumerate(q.states):
            action_scores = {}
            minimizing = {}
            for a in q.baseline.feasible[s, x]:
                scores = [sum((p * v for p, v in zip(_row(model, s, x, a, q.states), game_opt[-1])), Fraction(0))
                          for model in q.nature_worlds]
                minimum = min(scores)
                action_scores[a] = minimum
                minimizing[a] = [name for name, score in zip(q.nature_ids, scores) if score == minimum]
            value = max(action_scores.values())
            optimal_values.append(value)
            argmax_rows.append([a for a in q.baseline.feasible[s, x] if action_scores[a] == value])
            argmin_rows.append(minimizing)
            fixed_action = q.policy[i]
            fixed_scores = [sum((p * v for p, v in zip(_row(model, s, x, fixed_action, q.states), fixed_rect[-1])), Fraction(0))
                            for model in q.nature_worlds]
            fixed_values.append(min(fixed_scores))
            fixed_choices.append([name for name, score in zip(q.nature_ids, fixed_scores) if score == min(fixed_scores)])
        fixed_rect.append(_checked(tuple(fixed_values)))
        game_opt.append(_checked(tuple(optimal_values)))
        game_argmax.append(argmax_rows)
        game_argmin.append(argmin_rows)
        fixed_argmin.append(fixed_choices)
        for j, model in enumerate(q.nature_worlds):
            prior = committed[j][-1]
            values = tuple(sum((p * v for p, v in zip(_row(model, s, x, q.policy[i], q.states), prior)), Fraction(0))
                           for i, (s, x) in enumerate(q.states))
            committed[j].append(_checked(values))
    def serialize(table):
        return [[rational_text(t) for t in row] for row in table]
    worst_committed = tuple(min(committed[j][-1][i] for j in range(len(q.nature_ids))) for i in q.starts)
    fixed_rectangle = tuple(fixed_rect[-1][i] for i in q.starts)
    if any(a > b for a,b in zip(fixed_rectangle,worst_committed)):
        raise AppError('NATURE_INTERNAL', 'fixed rectangular value above committed bound')
    return {
        'format': RECEIPT,
        'request_identity': q.identity,
        'baseline_identity': q.baseline.semantic_id(),
        'nature_ids': list(q.nature_ids),
        'nature_model_identities': [model.semantic_id() for model in q.nature_worlds],
        'joint_states': [{'s':s,'x':x} for s,x in q.states],
        'comparison_indices': list(q.starts),
        'horizon': q.horizon,
        'terminal_rewards': [rational_text(r) for r in q.rewards],
        'fixed_policy_actions': list(q.policy),
        'rectangular_optimal_values_by_remaining': serialize(game_opt),
        'rectangular_argmax_by_remaining': game_argmax,
        'rectangular_minimizers_by_action': game_argmin,
        'fixed_policy_rectangular_values_by_remaining': serialize(fixed_rect),
        'fixed_policy_rectangular_minimizers': fixed_argmin,
        'fixed_policy_committed_values_by_nature': [serialize(x) for x in committed],
        'comparison': {
            'fixed_rectangular': [rational_text(v) for v in fixed_rectangle],
            'fixed_committed_worst': [rational_text(v) for v in worst_committed],
            'fixed_rectangular_minus_committed': [rational_text(a-b) for a,b in zip(fixed_rectangle,worst_committed)],
            'rectangular_optimized': [rational_text(game_opt[-1][i]) for i in q.starts],
        },
        'policy_class': 'fully_observed_deterministic_remaining_horizon_rectangular_and_fixed_stationary_for_committed',
        'nature_timing': 'after_realized_control_independent_row_reselection_vs_one_model_committed_at_time_zero',
        'committed_scope': 'declared_fixed_policy_only_not_committed_game_optimum',
        'strategic_alpha_and_U_held_fixed': True,
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
