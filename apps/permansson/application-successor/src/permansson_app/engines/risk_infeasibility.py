"""Exact Farkas certificate that a one-step risk cap cannot be met.

Same request as `one-step-risk`. For every joint state the floor v(y) is the
least next-step risk probability over the declared feasible actions (the mass
of the actual P·U row on the risk set), and the receipt lists every action
attaining it. The least risk mass of any fully observed randomized policy from
the initial law is Σ_y μ(y) v(y), attained by a pure floor policy, so the cap
is infeasible exactly when that total exceeds it. Then (v, risk-cap
multiplier 1) is a normalized Farkas ray of the occupancy program. When the
cap can be met this profile refuses; `one-step-risk` is the route to the
optimum. One transition only.
"""
from __future__ import annotations
from fractions import Fraction
from ..errors import AppError
from ..identity import rational_text
from .risk_occupancy import parse_risk

RECEIPT = 'Permansson.App.OneStepRiskInfeasibilityReceipt.v1'


def propose_risk_infeasibility(raw: object) -> dict:
    q = parse_risk(raw)
    floors, attaining = [], []
    for i, (s, x) in enumerate(q.states):
        risks = {a: r for (j, a), r in zip(q.variables, q.risk_coeffs) if j == i}
        low = min(risks.values())
        floors.append(low)
        attaining.append([a for a in q.model.feasible[s, x] if risks[a] == low])
    minimum = sum((m * v for m, v in zip(q.initial, floors)), Fraction(0))
    if minimum <= q.risk_cap:
        raise AppError('RISK_CAP_FEASIBLE', 'a floor policy meets the cap; use one-step-risk for the optimum')
    return {
        'format': RECEIPT,
        'request_identity': q.identity,
        'source_model_identity': q.model.semantic_id(),
        'joint_states': [{'s': s, 'x': x} for s, x in q.states],
        'risk_indices': list(q.risk_states),
        'risk_cap': rational_text(q.risk_cap),
        'initial_law': [rational_text(v) for v in q.initial],
        'risk_coefficients': [{'state_index': i, 'action': a, 'risk': rational_text(r)}
                              for (i, a), r in zip(q.variables, q.risk_coeffs)],
        'state_risk_floors': [rational_text(v) for v in floors],
        'floor_actions': attaining,
        'minimal_risk_probability': rational_text(minimum),
        'cap_shortfall': rational_text(minimum - q.risk_cap),
        'farkas_ray': {'mass_multipliers': [rational_text(v) for v in floors], 'risk_cap_multiplier': '1'},
        'status': 'RISK_CAP_INFEASIBLE',
        'optimization_scope': 'one_transition_fully_observed_randomized_Markov_from_declared_initial_law',
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
