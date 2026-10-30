"""Two closed native providers plus separately scoped exact numeric profiles."""
import json
from .package_data import resource_bytes
from .errors import AppError


def registry():
    data = json.loads(resource_bytes("capabilities.json"))
    caps = data.get("capabilities")
    if not isinstance(caps, dict) or set(caps) != {"c10.fixed_six_state.numeric.v1", "c11.stationary_1_to_6.numeric.v1"}:
        raise AppError("REGISTRY", "invalid registry capability set")
    extra=data.get('exact_profiles')
    if (type(extra) is not dict or set(extra)!={
        'finite.alpha_P_U.induced_kernel.numeric.v1',
        'finite.killed_kernel.survival.numeric.v1',
        'lp.exact_rational.optimality.numeric.v1',
        'lp.exact_rational.independent_verification.v1',
        'finite.random_occupation.numeric.v1',
        'finite.first_exit_and_survival.numeric.v1',
        'finite.frozen_menu.numeric.v1',
        'finite.hitting_bellman.numeric.v1',
        'finite.almost_sure_safety_core.numeric.v1',
        'finite.path_perturbation_tv.numeric.v1',
        'finite.residence_monitor.numeric.v1',
        'finite.nonlinear_classwise_stationary.numeric.v1',
        'finite.patch_grammar.numeric.v1',
        'finite.typed_quotient.numeric.v1',
        'finite.rectangular_vs_committed_nature.numeric.v1',
        'finite.one_step_risk_occupancy.numeric.v1',
        'finite.one_step_observation_belief.numeric.v1',
        'finite.observation_history_tree.numeric.v1',
        'finite.cq1_constitutive_certificate.numeric.v1',
        'finite.metric_contraction_perturbation.numeric.v1',
        'finite.rational_algebra_witness.numeric.v1',
        'finite.two_player_protocol.numeric.v1',
        'finite.private_control_stage_saddle.numeric.v1'}):
        raise AppError('REGISTRY','unknown or missing additive numeric profile')
    for name,entry in extra.items():
        if type(entry) is not dict or entry.get('mode')!='numeric' or entry.get('scientific_claims_verified') is not False or entry.get('lean_status')!='NOT_EXECUTED':
            raise AppError('REGISTRY','additive profile may not claim Lean or scientific certification')
    return data


def selected(key: str):
    c = registry()["capabilities"].get(key)
    if c is None:
        raise AppError("UNSUPPORTED_CAPABILITY", "not a supported numeric capability")
    return c
