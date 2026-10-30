"""Independent exact checker for one-step risk-cap infeasibility receipts.

Does not import the risk producers or the occupancy LP encoder. Re-reads the
original model, initial law, risk event and cap, recomposes every feasible
action's actual P·U row, and checks the Farkas ray directly: every admitted
action's risk is at least its state's multiplier, some admitted action
attains it, and the initial-law total of the multipliers exceeds the cap.
Together these prove that every randomized one-step policy exceeds the cap.
It is not a Lean proof or an independent certification.
"""
from __future__ import annotations
from fractions import Fraction
from hashlib import sha256
from ..errors import AppError
from ..finite_world import parse_finite_world, exact_ratio
from ..identity import canonical_bytes, semantic_identity, rational_text

REQUEST = 'Permansson.App.OneStepRiskOccupancyRequest.v1'
RECEIPT = 'Permansson.App.OneStepRiskInfeasibilityReceipt.v1'


def _fail(msg):
    raise AppError('RISK_INFEASIBILITY_RECEIPT', msg)


def check_risk_infeasibility(raw: object, receipt: object) -> dict:
    if (type(raw) is not dict or raw.get('format') != REQUEST or type(receipt) is not dict
            or set(raw) != {'format', 'model', 'initial_law', 'terminal_rewards', 'risk_states', 'risk_cap'}):
        _fail('unsupported request or receipt')
    m = parse_finite_world(raw['model'])
    states = [(s, x) for s in m.strategic for x in m.world]
    if len(states) > 4:
        _fail('state bound')
    law = [None] * len(states)
    for item in raw['initial_law']:
        law[states.index(tuple(item['state']))] = exact_ratio(item['mass'], probability=True)
    if any(v is None for v in law) or sum(law, Fraction(0)) != 1:
        _fail('initial law')
    risky = {states.index(tuple(pair)) for pair in raw['risk_states']}
    cap = exact_ratio(raw['risk_cap'], probability=True)
    mult = receipt.get('farkas_ray', {}).get('mass_multipliers')
    if type(mult) is not list or len(mult) != len(states) or receipt['farkas_ray'].get('risk_cap_multiplier') != '1':
        _fail('Farkas ray shape')
    v = [exact_ratio(t) for t in mult]
    coefficients, attaining = [], []
    for i, (s, x) in enumerate(states):
        hits = []
        for a in m.feasible[s, x]:
            risk = Fraction(0)
            for j, (sp, xp) in enumerate(states):
                if j in risky:
                    risk += m.P[s, x, a][m.world.index(xp)] * m.U[s, x, a, xp][m.strategic.index(sp)]
            if risk < v[i]:
                _fail('an admitted action falls below its state multiplier')
            if risk == v[i]:
                hits.append(a)
            coefficients.append({'state_index': i, 'action': a, 'risk': rational_text(risk)})
        if not hits:
            _fail('a state multiplier is not attained by an admitted action')
        attaining.append(hits)
    total = sum((p * w for p, w in zip(law, v)), Fraction(0))
    if not cap < total:
        _fail('the multipliers do not separate the cap')
    expected = {
        'format': RECEIPT,
        'request_identity': semantic_identity('one-step-risk-occupancy', raw),
        'source_model_identity': m.semantic_id(),
        'joint_states': [{'s': s, 'x': x} for s, x in states],
        'risk_indices': sorted(risky),
        'risk_cap': rational_text(cap),
        'initial_law': [rational_text(p) for p in law],
        'risk_coefficients': coefficients,
        'state_risk_floors': [rational_text(w) for w in v],
        'floor_actions': attaining,
        'minimal_risk_probability': rational_text(total),
        'cap_shortfall': rational_text(total - cap),
        'farkas_ray': {'mass_multipliers': [rational_text(w) for w in v], 'risk_cap_multiplier': '1'},
        'status': 'RISK_CAP_INFEASIBLE',
        'optimization_scope': 'one_transition_fully_observed_randomized_Markov_from_declared_initial_law',
        'lean_status': 'NOT_EXECUTED',
        'empirical_identification': 'NOT_IDENTIFIED',
        'scientific_claims_verified': False,
    }
    for key, value in expected.items():
        if receipt.get(key) != value:
            _fail(key + ' mismatch')
    if set(receipt) != set(expected):
        _fail('receipt fields mismatch')
    return {'format': 'Permansson.App.IndependentRiskInfeasibilityCheck.v1', 'status': 'INFEASIBILITY_VERIFIED',
            'minimal_risk_probability': rational_text(total), 'risk_cap': rational_text(cap),
            'receipt_sha256': sha256(canonical_bytes(receipt)).hexdigest(),
            'lean_status': 'NOT_EXECUTED', 'scientific_claims_verified': False}
