"""Finite exact greatest *almost-sure* controlled-invariant safe core.

Numerical analogue of ReverseSolver/GreatestControlledInvariant.lean.
This does not compute the probability of survival from an excluded state;
that probability can be positive even when no action gives almost-sure safety.
No new Lean correspondence or empirical identity is asserted here.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from ..errors import AppError
from ..finite_world import FiniteWorld, parse_finite_world
from ..identity import semantic_identity

FORMAT = 'Permansson.App.FiniteSafetyCore.v1'
RECEIPT = 'Permansson.App.FiniteSafetyCoreReceipt.v1'
MAX_STATES = 12

@dataclass(frozen=True)
class SafetyProblem:
    model: FiniteWorld
    safe_indices: tuple[int, ...]
    identity: dict


def parse_safety_problem(raw: object) -> SafetyProblem:
    if type(raw) is not dict or set(raw) != {'format','model','safe'} or raw['format'] != FORMAT:
        raise AppError('SAFETY_INPUT', 'exact versioned finite safety input required')
    m = parse_finite_world(raw['model'])
    states = [(s,x) for s in m.strategic for x in m.world]
    if len(states) > MAX_STATES:
        raise AppError('SAFETY_SCOPE','maximum 12 joint states')
    if type(raw['safe']) is not list or not raw['safe'] or len(raw['safe']) > len(states):
        raise AppError('SAFETY_INPUT','safe region must be nonempty and contain declared states')
    out = set()
    for pair in raw['safe']:
        if type(pair) is not dict or set(pair) != {'strategic','world'} or any(type(v) is not str for v in pair.values()):
            raise AppError('SAFETY_INPUT','invalid typed safe-state record')
        key = (pair['strategic'],pair['world'])
        if key not in states or states.index(key) in out:
            raise AppError('SAFETY_INPUT','foreign or repeated safe state')
        out.add(states.index(key))
    ordered = tuple(sorted(out))
    sid = semantic_identity('finite-safety-core',{'format':FORMAT,'model':m.semantic_id(),'safe_indices':list(ordered)})
    return SafetyProblem(m, ordered, sid)


def propose_safety_core(problem: SafetyProblem) -> dict:
    model = problem.model
    states = tuple((s,x) for s in model.strategic for x in model.world)
    support = {}
    for i,(s,x) in enumerate(states):
        for a in model.feasible[s,x]:
            idx = []
            for j,(sp,xp) in enumerate(states):
                if model.P[s,x,a][model.world.index(xp)] * model.U[s,x,a,xp][model.strategic.index(sp)] > 0:
                    idx.append(j)
            support[i,a] = frozenset(idx)
    core = set(problem.safe_indices)
    chain = [sorted(core)]
    # |G| strict removals at most. One final iteration witnesses the fixed point.
    for _ in range(len(problem.safe_indices) + 1):
        next_set = {i for i in core if any(support[i,a] <= core for a in model.feasible[states[i]])}
        chain.append(sorted(next_set))
        if next_set == core:
            break
        core = next_set
    else:
        raise AppError('SAFETY_INTERNAL','finite pruning did not stabilize at cardinality bound')
    witness = []
    for i in sorted(core):
        a = next(a for a in model.feasible[states[i]] if support[i,a] <= core)
        witness.append({'state_index':i,'action':a})
    return {'format':RECEIPT,'problem_semantic_identity':problem.identity,
            'model_semantic_identity':model.semantic_id(),
            'joint_states':[{'strategic':s,'world':x} for s,x in states],
            'initial_safe_indices':list(problem.safe_indices),
            'descending_pruning_chain':chain,'core_indices':sorted(core),
            'stationary_witness_actions':witness,
            'scope':'GREATEST_ALMOST_SURE_CONTROLLED_INVARIANT_SUBSET',
            'outside_core':'NOT_ALMOST_SURE_SAFE_NO_ZERO_SURVIVAL_PROBABILITY_INFERRED',
            'baseline_alpha_policy_optimized_over':True,
            'lean_status':'NOT_EXECUTED',
            'empirical_identification':'NOT_IDENTIFIED',
            'scientific_claims_verified':False}
