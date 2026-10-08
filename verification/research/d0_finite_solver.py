"""D0 exact rational evaluator for a finite *frozen* menu of Markov kernels.

This is a mathematical evaluator for explicit finite inputs, NOT a bridge
certifying that an arbitrary matrix is an admissible strategic-world intervention.
The Lean D0 menu separately accepts typed admissible strategic interventions.

Each candidate is a single time-homogeneous kernel held fixed for all T steps.
No search outside the enumerated menu and no adaptive policy synthesis.
"""
from fractions import Fraction
from dataclasses import dataclass

Q = Fraction


def validate_kernel(rows):
    """Check a nonempty finite row-stochastic kernel with exact rational rows."""
    n = len(rows)
    if not n:
        raise ValueError("empty state space")
    if any(len(row) != n or any(p < 0 for p in row)
           or sum(row, Q(0)) != 1 for row in rows):
        raise ValueError("invalid stochastic kernel")
    return n


def validate_target(n, goal, forbidden, initial, horizon):
    if not isinstance(horizon, int) or horizon < 0:
        raise ValueError("negative or nonintegral horizon")
    universe = set(range(n))
    if not set(goal) <= universe or not set(forbidden) <= universe:
        raise ValueError("target/forbidden outside state space")
    if set(goal) & set(forbidden):
        raise ValueError("target and forbidden must be disjoint")
    if initial not in universe:
        raise ValueError("initial outside state space")


def success(path, goal, forbidden):
    """A target at t<=T, and no forbidden state at an earlier index."""
    for t, y in enumerate(path):
        if y in goal and not any(path[u] in forbidden for u in range(t)):
            return True
    return False


def prefix_law(rows, initial, horizon):
    """Exact finite paths under the same stationary row kernel at each time."""
    n = validate_kernel(rows)
    if initial not in range(n) or horizon < 0:
        raise ValueError("invalid initial/horizon")
    law = {(initial,): Q(1)}
    for _ in range(horizon):
        nxt = {}
        for path, mass in law.items():
            for dest, prob in enumerate(rows[path[-1]]):
                if prob:
                    new_path = path + (dest,)
                    nxt[new_path] = nxt.get(new_path, Q(0)) + mass * prob
        law = nxt
    return law


def value_by_enumeration(rows, initial, goal, forbidden, horizon):
    n = validate_kernel(rows)
    validate_target(n, goal, forbidden, initial, horizon)
    return sum((mass for path, mass in prefix_law(rows, initial, horizon).items()
                if success(path, goal, forbidden)), Q(0))


def value_by_recursion(rows, initial, goal, forbidden, horizon):
    """Exact D0 backward hitting recursion (numerical, not yet a Lean bridge)."""
    n = validate_kernel(rows)
    validate_target(n, goal, forbidden, initial, horizon)
    g, d = set(goal), set(forbidden)
    v = [Q(int(y in g)) for y in range(n)]
    for _ in range(horizon):
        v = [Q(1) if y in g else Q(0) if y in d else
             sum((rows[y][z] * v[z] for z in range(n)), Q(0))
             for y in range(n)]
    return v[initial]


@dataclass(frozen=True)
class FixedMenuResult:
    selected: str
    value: Q
    values: tuple
    scope: str = "EXACT_FINITE_MENU_CALCULATION"


def solve_frozen_menu(menu, initial, goal, forbidden, horizon):
    """Enumerate every named fixed candidate; tie breaks by frozen menu order."""
    items = tuple(menu)
    if not items:
        raise ValueError("empty intervention menu")
    names = [name for name, _ in items]
    if len(names) != len(set(names)):
        raise ValueError("duplicate menu labels")
    vals = []
    for name, rows in items:
        v = value_by_recursion(rows, initial, goal, forbidden, horizon)
        vals.append((name, v))
    chosen = max(vals, key=lambda pair: pair[1])
    return FixedMenuResult(chosen[0], chosen[1], tuple(vals))
