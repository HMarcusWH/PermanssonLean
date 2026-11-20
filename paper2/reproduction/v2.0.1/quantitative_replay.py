"""New exact reproductions of the 43 retained quantitative review results.

This is newly authored reproduction code, not a recovered original review
program.  Inputs and formulas come from the reviewed v2.0.1 manuscript.  The
module never reads the retained JSON results: comparison with those records is
the responsibility of the separate reproduction runner.

In particular, the Q05 values are obtained by solving finite discounted
Bellman systems assembled from the stated action/world/update primitives;
they are not assigned the closed-form values printed in the manuscript.

The retained endpoint records do not specify their original free parameters.
These new witnesses choose beta = 1/3 for eta = 0 and eta = 1/20 for beta = 0,
both parameters used in the manuscript's Q05 fixture.  The unit-defect witness
uses one defect equal to one followed by a zero tail.  These are explicit
reproductions of the stated identities, not claims to recover missing inputs.

Only Python's standard library and exact fractions are used.  This module
does not compile Lean or certify the general path-law theorems.
"""

from __future__ import annotations

from fractions import Fraction as F
from itertools import product


_F_BOOLEAN = "appendices/F_grammar.tex :: F:boolean"
_DEPENDENT = "sections/C13.tex :: C13:witnesses; appendices/G_path_transport.tex :: G:fixtures"
_Q04 = "appendices/G_path_transport.tex :: G:q04"
_Q05 = "appendices/G_path_transport.tex :: G:fixtures; sections/C13.tex :: C13:witnesses"
_DISCOUNT = "sections/C13.tex :: eq:C13:discountbudget; appendices/G_path_transport.tex :: G:discount"
_RETAINED = "sections/C13.tex :: C13:wholepath; appendices/G_path_transport.tex :: G:fullpath"
_MOMENT = "appendices/A_foundations.tex :: app:A; appendices/H_metric_occupation.tex :: H:regeneration"


def _record(name: str, actual: object, source: str, calculation: str) -> dict:
    return {"name": name, "actual": str(actual), "source": source, "calculation": calculation}


def _boolean_destinations() -> list[tuple[int, int]]:
    """Apply action then x' = a then the strategic-state update."""
    destinations = []
    for patch_action, patch_update in ((False, False), (True, False),
                                       (False, True), (True, True)):
        action = 0 if patch_action else 1
        next_world = action
        next_strategy = 0 if patch_update else 1
        destinations.append((next_strategy, next_world))
    return destinations


def _conditional_event(start: tuple[int, int], destination: tuple[int, int]) -> int:
    """The actual cylinder event in Appendix F, not patch-label membership."""
    return int(destination == (0, 0) or (start == (1, 0) and destination == (1, 0)))


def _dependent_history_law(defects: tuple[F, ...]) -> dict[tuple[int, ...], F]:
    """A first failure forces all subsequent observations to fail."""
    law = {(): F(1)}
    for defect in defects:
        if not F(0) <= defect <= F(1):
            raise ValueError("Defects must be probabilities.")
        extended = {}
        for history, mass in law.items():
            alive = not history or history[-1] == 1
            branches = ((0, defect), (1, 1 - defect)) if alive else ((0, F(1)),)
            for observation, probability in branches:
                if probability:
                    key = history + (observation,)
                    extended[key] = extended.get(key, F(0)) + mass * probability
        law = extended
    return law


def _event_tv(left: dict, right: dict) -> F:
    """Compute the finite event supremum, rather than assuming half-l1."""
    atoms = sorted(left.keys() | right.keys())
    largest = F(0)
    for selected in product((False, True), repeat=len(atoms)):
        discrepancy = sum((left.get(atom, F(0)) - right.get(atom, F(0)))
                          for atom, include in zip(atoms, selected) if include)
        largest = max(largest, abs(discrepancy))
    return F(largest)


def _q04_step(state: tuple[int, int], *, treated: bool, approximate: bool) -> tuple[int, int]:
    strategy, world = state
    action = 0 if treated else 1
    if action == 1:
        next_world = world
    else:
        next_world = 1 - world if approximate else 1
    return strategy, next_world


def _q04_orbit(strategy: int, *, treated: bool, approximate: bool,
               transitions: int = 2) -> list[tuple[int, int]]:
    state = (strategy, 0)
    orbit = [state]
    for _ in range(transitions):
        state = _q04_step(state, treated=treated, approximate=approximate)
        orbit.append(state)
    return orbit


def _solve(matrix: list[list[F]], rhs: list[F]) -> list[F]:
    """Exact Gaussian elimination with row swaps for a square finite system."""
    dimension = len(rhs)
    if len(matrix) != dimension or any(len(row) != dimension for row in matrix):
        raise ValueError("Expected a square system.")
    augmented = [[F(value) for value in row] + [F(rhs[i])]
                 for i, row in enumerate(matrix)]
    for column in range(dimension):
        pivot = next((row for row in range(column, dimension)
                      if augmented[row][column]), None)
        if pivot is None:
            raise ValueError("Singular rational system.")
        augmented[column], augmented[pivot] = augmented[pivot], augmented[column]
        divisor = augmented[column][column]
        augmented[column] = [value / divisor for value in augmented[column]]
        for row in range(dimension):
            if row != column:
                factor = augmented[row][column]
                augmented[row] = [value - factor * pivot_value
                                  for value, pivot_value in zip(augmented[row], augmented[column])]
    answer = [row[-1] for row in augmented]
    # Check the original equations, independently of the elimination state.
    if any(sum(a * x for a, x in zip(row, answer)) != value
           for row, value in zip(matrix, rhs)):
        raise ArithmeticError("Rational solve did not satisfy its input system.")
    return answer


def _discounted_values(kernel: list[list[F]], rewards: list[F], beta: F) -> list[F]:
    """Solve V = (1-beta) g + beta K V for a normalized discounted score."""
    dimension = len(rewards)
    if not F(0) <= beta < F(1):
        raise ValueError("Discount factor must be in [0, 1).")
    if len(kernel) != dimension or any(len(row) != dimension for row in kernel):
        raise ValueError("Kernel and reward dimensions differ.")
    if any(sum(row) != 1 or any(probability < 0 for probability in row) for row in kernel):
        raise ValueError("Rows must be probability distributions.")
    matrix = [[F(int(i == j)) - beta * kernel[i][j] for j in range(dimension)]
              for i in range(dimension)]
    return _solve(matrix, [(1 - beta) * reward for reward in rewards])


_FINE_STATES = tuple(product((0, 1), repeat=2))


def _fine_kernel(action_success: tuple[F, F], next_strategy: int,
                 *, update_before_action: bool = False) -> list[list[F]]:
    """Q05 primitives.  The optional reversed order is only a negative control."""
    rows = []
    for strategy, _world in _FINE_STATES:
        probability = action_success[next_strategy if update_before_action else strategy]
        if not F(0) <= probability <= F(1):
            raise ValueError("Action probability outside [0, 1].")
        row = []
        for target_strategy, target_world in _FINE_STATES:
            value = probability if target_world else 1 - probability
            row.append(value if target_strategy == next_strategy else F(0))
        rows.append(row)
    return rows


def _coarse_kernel(action_success: F) -> list[list[F]]:
    return [[1 - action_success, action_success] for _world in (0, 1)]


def _projected_row_error(fine: list[list[F]], coarse: list[list[F]]) -> F:
    """Compress (s,x) to x and compare every projected row with its coarse row."""
    errors = []
    for row_index, (_strategy, world) in enumerate(_FINE_STATES):
        projected = {target_world: sum(fine[row_index][j]
                                     for j, (_s, x) in enumerate(_FINE_STATES)
                                     if x == target_world)
                     for target_world in (0, 1)}
        errors.append(_event_tv(projected, {x: coarse[world][x] for x in (0, 1)}))
    return max(errors)


def _discount_budget(beta: F, epsilon: F, eta: F) -> F:
    if not F(0) <= beta < F(1) or not F(0) <= epsilon <= F(1) or not F(0) <= eta <= F(1):
        raise ValueError("Budget parameters outside their probability/discount domain.")
    return 1 - (1 - epsilon) * (1 - beta) / (1 - beta * (1 - eta))


def _q05_fixture() -> dict:
    beta = F(1, 3)
    fine_baseline = _fine_kernel((F(1, 10), F(1, 5)), 0)
    fine_treatment = _fine_kernel((F(7, 10), F(4, 5)), 1)
    coarse_baseline = _coarse_kernel(F(3, 20))
    coarse_treatment = _coarse_kernel(F(3, 4))
    fine_rewards = [F(world) for _strategy, world in _FINE_STATES]
    coarse_rewards = [F(world) for world in (0, 1)]
    values = {
        "fine_baseline": _discounted_values(fine_baseline, fine_rewards, beta),
        "fine_treatment": _discounted_values(fine_treatment, fine_rewards, beta),
        "coarse_baseline": _discounted_values(coarse_baseline, coarse_rewards, beta),
        "coarse_treatment": _discounted_values(coarse_treatment, coarse_rewards, beta),
    }
    baseline_error = _projected_row_error(fine_baseline, coarse_baseline)
    treatment_error = _projected_row_error(fine_treatment, coarse_treatment)
    values["baseline_budget"] = _discount_budget(beta, F(0), baseline_error)
    values["treatment_budget"] = _discount_budget(beta, F(0), treatment_error)
    values["baseline_row_error"] = baseline_error
    values["treatment_row_error"] = treatment_error
    return values


def _retained_mass(defects: tuple[F, ...]) -> F:
    mass = F(1)
    for defect in defects:
        mass *= 1 - defect
    return mass


def compute_checks() -> list[dict]:
    """Compute exactly the 43 named retained outputs, with source provenance."""
    checks = []
    destinations = _boolean_destinations()
    observables = {
        "OR": lambda state: int(bool(state[0] or state[1])),
        "AND": lambda state: state[0] * state[1],
        "XOR": lambda state: int(state[0] != state[1]),
    }
    for name, observable in observables.items():
        values = [observable(state) for state in destinations]
        effects = [abs(value - values[0]) for value in values[1:]]
        checks.append(_record(name + "_values", values, _F_BOOLEAN,
                              "Evaluate the Boolean observable on each actual action/world/update destination."))
        checks.append(_record(name + "_effects", effects, _F_BOOLEAN,
                              "Absolute differences from the baseline observable value."))
    for start in ((1, 1), (1, 0)):
        values = [_conditional_event(start, destination) for destination in destinations]
        checks.append(_record("conditional_event_" + str(start), values, _F_BOOLEAN,
                              "Evaluate 1[Y1=(0,0) or (Y0=(1,0) and Y1=(1,0))] on canonical deterministic paths."))
    real_observable = {(1, 1): 0, (1, 0): 1, (0, 1): -1, (0, 0): 2}
    baseline, action, update, joint = [real_observable[state] for state in destinations]
    checks.append(_record("interaction_vector", joint - action - update + baseline, _F_BOOLEAN,
                          "Signed four-corner interaction v11-v10-v01+v00."))
    checks.append(_record("scalar_distance_subtraction",
                          abs(joint - baseline) - abs(action - baseline) - abs(update - baseline),
                          _F_BOOLEAN, "Subtract baseline distances, retaining the difference from signed interaction."))
    checks.append(_record("conditional_vector_legs", [abs(joint - action), abs(joint - update)],
                          _F_BOOLEAN, "Two conditional distances: |v11-v10| and |v11-v01|."))

    law = _dependent_history_law((F(1, 10), F(1, 5), F(1, 4)))
    checks.append(_record("three_stage_atoms", [law[atom] for atom in sorted(law)], _DEPENDENT,
                          "Append conditional Bernoulli stages; a failed history stays failed thereafter."))
    checks.append(_record("three_stage_mass", sum(law.values()), _DEPENDENT,
                          "Sum the exactly constructed dependent-history atom masses."))
    checks.append(_record("three_stage_event_TV", _event_tv(law, {(1, 1, 1): F(1)}), _DEPENDENT,
                          "Maximize absolute event-probability differences over all subsets of the finite support."))

    for strategy in (0, 1):
        values = [_q04_orbit(strategy, treated=treated, approximate=approximate)[-1][1]
                  for approximate, treated in ((False, False), (False, True), (True, False), (True, True))]
        checks.append(_record("Q04_values_" + str(strategy), values, _Q04,
                              "Apply the true/approximate baseline/treated physical rules for exactly two transitions; read x2."))

    fixture = _q05_fixture()
    fine_effects, coarse_effects = [], []
    for world in (0, 1):
        fine_index = _FINE_STATES.index((0, world))
        for model in ("fine_baseline", "fine_treatment", "coarse_baseline", "coarse_treatment"):
            index = fine_index if model.startswith("fine_") else world
            checks.append(_record("Q05_" + model + "_" + str(world), fixture[model][index], _Q05,
                                  "Exact rational solve of (I-beta K)V=(1-beta)g using the stated chronological primitives, beta=1/3."))
        fine_effect = abs(fixture["fine_treatment"][fine_index] - fixture["fine_baseline"][fine_index])
        coarse_effect = abs(fixture["coarse_treatment"][world] - fixture["coarse_baseline"][world])
        fine_effects.append(fine_effect)
        coarse_effects.append(coarse_effect)
        checks.append(_record("Q05_fine_effect_" + str(world), fine_effect, _Q05,
                              "Absolute treated-minus-baseline discounted value at the declared fine start."))
        checks.append(_record("Q05_coarse_effect_" + str(world), coarse_effect, _Q05,
                              "Absolute treated-minus-baseline discounted value at the corresponding coarse start."))
    fine_margin, coarse_margin = min(fine_effects), min(coarse_effects)
    checks.append(_record("Q05_margin_gap", abs(fine_margin - coarse_margin), _Q05,
                          "Difference between infima over the full two-start fine/coarse comparison sets."))
    if fixture["baseline_budget"] != fixture["treatment_budget"]:
        raise ArithmeticError("The two displayed Q05 score budgets unexpectedly differ.")
    checks.append(_record("Q05_score_budget", fixture["baseline_budget"], _Q05 + "; " + _DISCOUNT,
                          "Compute maximum projected-row event TV, then B_beta(0,eta) with beta=1/3."))
    margin_budget = fixture["baseline_budget"] + fixture["treatment_budget"]
    checks.append(_record("Q05_margin_budget", margin_budget, _Q05 + "; " + _DISCOUNT,
                          "Add the independently computed baseline and treated score budgets."))
    checks.append(_record("Q05_strict_positive_gap", fine_margin - margin_budget > 0, _Q05,
                          "Check strict positivity of the original fine margin after subtracting its transport budget."))

    for epsilon in (F(0), F(1, 4), F(1)):
        checks.append(_record("discount_zero_eta_" + str(epsilon),
                              _discount_budget(F(1, 3), epsilon, F(0)), _DISCOUNT,
                              "New explicit endpoint witness: beta=1/3, eta=0; retain the declared initial mismatch epsilon."))
        checks.append(_record("discount_zero_beta_" + str(epsilon),
                              _discount_budget(F(0), epsilon, F(1, 20)), _DISCOUNT,
                              "New explicit endpoint witness: beta=0, eta=1/20; only the time-zero mismatch remains."))
    checks.append(_record("single_unit_defect_retained_mass", _retained_mass((F(1),)), _RETAINED,
                          "One unit defect and a zero tail give the retained product (1-1)*1*1*...; the defect sum is finite."))
    for n in (1, 2, 10, 100):
        law_n = {0: 1 - F(1, n), n: F(1, n)}
        cost = sum(F(abs(location)) * mass for location, mass in law_n.items())
        checks.append(_record("escaping_mass_W1_" + str(n), cost, _MOMENT,
                              "Transport (1-1/n) delta_0 + (1/n) delta_n to delta_0: the unique target costs sum_x mass(x)|x|."))
    if len(checks) != 43 or len({row["name"] for row in checks}) != 43:
        raise ArithmeticError("The reproduction must expose exactly 43 unique retained names.")
    return checks


def negative_controls() -> list[dict]:
    """Separate adversarial checks; passed means an incorrect shortcut is rejected.

    These are newly added controls and are not part of the retained count 43.
    """
    controls = []

    def reject(name: str, wrong: object, correct: object, source: str, calculation: str) -> None:
        controls.append({"name": name, "actual": str(wrong), "expected": str(correct),
                         "passed": wrong != correct, "source": source, "calculation": calculation})

    destinations = _boolean_destinations()
    reject("patch_indicator_OR_is_not_state_OR", [int(a or u) for a, u in
           ((False, False), (True, False), (False, True), (True, True))],
           [int(s or x) for s, x in destinations], _F_BOOLEAN,
           "Reject interpreting source OR as OR of selected-patch indicators.")
    values = {(1, 1): 0, (1, 0): 1, (0, 1): -1, (0, 0): 2}
    b, a, u, j = [values[state] for state in destinations]
    reject("distance_subtraction_loses_signed_interaction", abs(j-b)-abs(a-b)-abs(u-b),
           j-a-u+b, _F_BOOLEAN, "Reject distance subtraction as the signed four-corner interaction.")
    law = _dependent_history_law((F(1, 10), F(1, 5), F(1, 4)))
    independent_success = F(1)
    for time in range(3):
        independent_success *= sum(mass for history, mass in law.items() if history[time] == 1)
    reject("independent_marginals_do_not_reconstruct_dependent_history", independent_success,
           law[(1, 1, 1)], _DEPENDENT,
           "Reject multiplying unconditional success marginals instead of conditional history rows.")
    baseline = _q04_orbit(0, treated=False, approximate=False)
    treated = _q04_orbit(0, treated=True, approximate=False)

    def treatment_row_error(state: tuple[int, int]) -> F:
        true_next = _q04_step(state, treated=True, approximate=False)
        approximate_next = _q04_step(state, treated=True, approximate=True)
        return _event_tv({true_next: F(1)}, {approximate_next: F(1)})

    baseline_budget = sum(treatment_row_error(state) for state in baseline[:-1])
    treated_budget = sum(treatment_row_error(state) for state in treated[:-1])
    true_margin = abs(treated[-1][1] - baseline[-1][1])
    approximate_margin = abs(_q04_orbit(0, treated=True, approximate=True)[-1][1]
                             - _q04_orbit(0, treated=False, approximate=True)[-1][1])
    lost_margin = F(abs(true_margin - approximate_margin))
    if treated_budget != lost_margin:
        raise ArithmeticError("The treated reference budget should identify the complete Q04 loss.")
    reject("baseline_only_visits_miss_treated_row_defect", baseline_budget, lost_margin,
           _Q04, "Reject charging only baseline visits; the treated reference pays its own row defect.")
    fixture = _q05_fixture()
    wrong_kernel = _fine_kernel((F(7, 10), F(4, 5)), 1, update_before_action=True)
    wrong_values = _discounted_values(wrong_kernel, [F(x) for _s, x in _FINE_STATES], F(1, 3))
    reject("updating_strategy_before_action_changes_Q05_score", wrong_values[0],
           fixture["fine_treatment"][0], _Q05,
           "Reject using the replacement strategic state before the action draw; the actual chronology uses the current state.")
    matching_start_shortcut = F(0) * F(1, 20) / (1 - F(0) + F(0) * F(1, 20))
    reject("matching_start_shortcut_drops_initial_mismatch", matching_start_shortcut,
           _discount_budget(F(0), F(1, 4), F(1, 20)), _DISCOUNT,
           "Reject substituting the epsilon=0 shortcut when the initial mismatch is one quarter.")
    return controls
