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


def _exact_rational(value):
    """Permit only Fraction and genuine int; never silently coerce float/bool."""
    if type(value) not in (int, Fraction):
        raise ValueError("transition entries must be exact int/Fraction values")
    return Fraction(value)


def validate_kernel(rows):
    """Check a nonempty finite row-stochastic kernel with exact rational rows."""
    n = len(rows)
    if not n:
        raise ValueError("empty state space")
    for row in rows:
        if len(row) != n:
            raise ValueError("non-square stochastic matrix")
        weights = tuple(_exact_rational(p) for p in row)
        if any(p < 0 for p in weights) or sum(weights, Q(0)) != 1:
            raise ValueError("invalid stochastic row")
    return n


def validate_target(n, goal, forbidden, initial, horizon):
    """Validate once and return immutable target sets, including one-shot iterables.

    Never validate a generator and then pass the exhausted generator onward.
    """
    if type(horizon) is not int or horizon < 0:
        raise ValueError("negative or nonintegral horizon")
    universe = set(range(n))
    goal_items, forbidden_items = tuple(goal), tuple(forbidden)
    if any(type(s) is not int for s in goal_items + forbidden_items):
        raise ValueError("target/forbidden indices must be integers")
    g, d = frozenset(goal_items), frozenset(forbidden_items)
    if not g <= universe or not d <= universe:
        raise ValueError("target/forbidden outside state space")
    if g & d:
        raise ValueError("target and forbidden must be disjoint")
    if type(initial) is not int or initial not in universe:
        raise ValueError("initial outside state space")
    return g, d


def success(path, goal, forbidden):
    """A target at t<=T, and no forbidden state at an earlier index."""
    for t, y in enumerate(path):
        if y in goal and not any(path[u] in forbidden for u in range(t)):
            return True
    return False


def prefix_law(rows, initial, horizon):
    """Exact finite paths under the same stationary row kernel at each time."""
    n = validate_kernel(rows)
    if type(initial) is not int or initial not in range(n) or type(horizon) is not int or horizon < 0:
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
    g, d = validate_target(n, goal, forbidden, initial, horizon)
    return sum((mass for path, mass in prefix_law(rows, initial, horizon).items()
                if success(path, g, d)), Q(0))


class RationalBitBudgetExceeded(ValueError):
    """Exact calculation exceeded an optional bit-size resource budget."""


def _check_exact_bit_budget(value, max_rational_bits):
    if max_rational_bits is not None and (
            max(abs(value.numerator).bit_length(),
                value.denominator.bit_length()) > max_rational_bits):
        raise RationalBitBudgetExceeded("backward rational bit limit")


def value_by_recursion(rows, initial, goal, forbidden, horizon, *, max_rational_bits=None):
    """Exact D0 backward recursion; optional intermediate rational-size guard.

    The default remains the original unbounded mathematical evaluator.
    Report generation supplies a finite budget and checks each product and
    partial row sum, not merely the final answer (which may simplify to 0).
    """
    n = validate_kernel(rows)
    g, d = validate_target(n, goal, forbidden, initial, horizon)
    if max_rational_bits is not None and (
            type(max_rational_bits) is not int or max_rational_bits <= 0):
        raise ValueError("invalid rational bit budget")
    v = [Q(int(y in g)) for y in range(n)]
    for _ in range(horizon):
        updated = []
        for y in range(n):
            if y in g:
                total = Q(1)
            elif y in d:
                total = Q(0)
            else:
                total = Q(0)
                for z in range(n):
                    term = rows[y][z] * v[z]
                    _check_exact_bit_budget(term, max_rational_bits)
                    total += term
                    _check_exact_bit_budget(total, max_rational_bits)
            updated.append(total)
        v = updated
    return v[initial]


@dataclass(frozen=True)
class FixedMenuResult:
    selected: str
    value: Q
    values: tuple
    scope: str = "EXACT_FINITE_MENU_CALCULATION"


def solve_frozen_menu(menu, initial, goal, forbidden, horizon, *, max_rational_bits=None):
    """Enumerate every named fixed candidate; tie breaks by frozen menu order.

    Optional finite bit budget applies to every backward intermediate value.
    """
    items = tuple(menu)
    if not items:
        raise ValueError("empty intervention menu")
    names = [name for name, _ in items]
    if len(names) != len(set(names)):
        raise ValueError("duplicate menu labels")
    dimensions = [validate_kernel(rows) for _, rows in items]
    if len(set(dimensions)) != 1:
        raise ValueError("menu kernels must share one state space")
    g, d = validate_target(dimensions[0], goal, forbidden, initial, horizon)
    vals = []
    for name, rows in items:
        v = value_by_recursion(rows, initial, g, d, horizon,
                               max_rational_bits=max_rational_bits)
        vals.append((name, v))
    chosen = max(vals, key=lambda pair: pair[1])
    assert type(chosen[1]) is Fraction and all(type(v) is Fraction for _, v in vals)
    return FixedMenuResult(chosen[0], chosen[1], tuple(vals))


def verify_frozen_menu_result(menu, initial, goal, forbidden, horizon, reported):
    """Independently re-evaluate a candidate report by exhaustive path sums.

    This is a second exact Python computation, NOT a Lean-verified software
    certificate and NOT a proof that arbitrary matrices are typed interventions.
    """
    if (not isinstance(reported, FixedMenuResult)
            or reported.scope != "EXACT_FINITE_MENU_CALCULATION"
            or type(reported.value) is not Q):
        return False
    items = tuple(menu)
    if not items or len({name for name, _ in items}) != len(items):
        raise ValueError("invalid frozen menu")
    dimensions = [validate_kernel(rows) for _, rows in items]
    if len(set(dimensions)) != 1:
        raise ValueError("menu kernels must share one state space")
    g, d = validate_target(dimensions[0], goal, forbidden, initial, horizon)
    expected = tuple((name, value_by_enumeration(rows, initial, g, d, horizon))
                     for name, rows in items)
    if tuple(reported.values) != expected or any(type(v) is not Q for _, v in reported.values):
        return False
    best = max(expected, key=lambda pair: pair[1])
    return reported.selected == best[0] and reported.value == best[1]


