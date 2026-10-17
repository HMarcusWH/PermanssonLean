"""Exact X1 commons calculations; no occupation-convergence or PR promotion.

Reuses the committed handover's rational candidate and transition semantics,
with explicit frozen comparison data and import-safe functions. Lean's typed
models use the same parameters; these calculations remain executable evidence.
"""
from fractions import Fraction as F
from itertools import product

BOOL = (False, True)
ACTIONS = tuple(product(BOOL, repeat=2))
STATES = tuple(((i, j), x) for i in range(3) for j in range(3) for x in BOOL)
START = ((1, 1), True)
REGION = frozenset(y for y in STATES if y[1])
POINTWISE_STARTS = frozenset({START})
# Prospective design v2: the original singleton comparison fails the core's
# two-start pathLawNontrivial gate. The whole already-fixed region is now used,
# before computing ANY comparison infimum. No outcome-based subset selection.
BASIN = COMPARISON_STARTS = REGION
PROPERTY_HORIZON = 3
BETA, CHI, COST, EPS = F(9, 10), F(193, 211), F(1, 10), F(1, 10)


def p_rep(x, a):
    return min(F(1), max(F(0), (F(9, 10) if x else F(1, 4)) - F(1, 4) * sum(a)))


def world(y, a):
    p = p_rep(y[1], a)
    return {True: p, False: 1-p}


def reward(i, x, a, chi=CHI):
    return (F(1, 2) if x else 0) * a[i] - chi * a[i] * a[1-i] - COST * (not x)


def value(i, x):
    return F(-81 if x else -121, 211)


def extraction(mode, y):
    if mode == "E":
        return (F(1, 2) if y[1] else F(0),) * 2
    if mode == "L":
        return tuple((1-EPS) * F(q, 2) + EPS / 2 for q in y[0])
    raise ValueError("Unknown strategic mode")


def action_law(mode, y, restrain=False):
    if restrain:
        return {(False, False): F(1)}
    p, q = extraction(mode, y)
    return {a: (p if a[0] else 1-p) * (q if a[1] else 1-q) for a in ACTIONS}


def update(mode, y, a, reset=False):
    if reset:
        return (1, 1)
    if mode == "E":
        return y[0]
    ref = F(1 if y[1] else -1, 20)
    def advance(i):
        gap = reward(i, y[1], a) - ref
        sign = (gap > 0) - (gap < 0)
        return min(2, max(0, y[0][i] + (2 * a[i]-1) * sign))
    return (advance(0), advance(1))


def kernel(mode, restrain=False, reset=False, physical_world=world):
    """The SAME physical world function is called in alpha -> P -> U order."""
    matrix = {}
    for y in STATES:
        row = {}
        for a, pa in action_law(mode, y, restrain).items():
            for x, px in physical_world(y, a).items():
                q = update(mode, y, a, reset)
                z = (q, x)
                row[z] = row.get(z, F(0)) + pa * px
        matrix[y] = {z: p for z, p in row.items() if p}
        if any(p < 0 for p in matrix[y].values()) or sum(matrix[y].values()) != 1:
            raise ValueError("Invalid probability row")
    return matrix


def deviation(i, x, own, chi=CHI, physical_world=world):
    p = F(1, 2) if x else F(0)
    total = F(0)
    for other in BOOL:
        a = (own, other) if i == 0 else (other, own)
        continuation = sum(mass * value(i, z) for z, mass in physical_world(((1, 1), x), a).items())
        total += (p if other else 1-p) * (reward(i, x, a, chi) + BETA * continuation)
    return total


def reachable(K, start=START):
    seen, pending = {start}, [start]
    while pending:
        for z in K[pending.pop()]:
            if z not in seen:
                seen.add(z)
                pending.append(z)
    return seen


def stationary(K, states):
    """Exact linear solve only. No ergodic/pathwise convergence is inferred."""
    states = tuple(sorted(states))
    n = len(states)
    A = [[K[y].get(z, F(0)) - (i == j) for j, y in enumerate(states)]
         for i, z in enumerate(states)]
    A[-1] = [F(1)] * n
    rhs = [F(0)] * (n-1) + [F(1)]
    for c in range(n):
        pivot = next(r for r in range(c, n) if A[r][c])
        A[c], A[pivot] = A[pivot], A[c]
        rhs[c], rhs[pivot] = rhs[pivot], rhs[c]
        scale = A[c][c]
        A[c], rhs[c] = [v / scale for v in A[c]], rhs[c] / scale
        for r in range(n):
            if r != c:
                scale = A[r][c]
                A[r] = [u-scale*v for u, v in zip(A[r], A[c])]
                rhs[r] -= scale * rhs[c]
    return dict(zip(states, rhs))


def killed_persistence(K, horizon, start=START):
    v = {y: F(y in REGION) for y in STATES}
    for _ in range(horizon):
        v = {y: sum((p*v[z] for z, p in K[y].items() if z in REGION), F(0))
             if y in REGION else F(0) for y in STATES}
    return v[start]


def replete_at(K, horizon=PROPERTY_HORIZON, start=START):
    law = {start: F(1)}
    for _ in range(horizon):
        nxt = {}
        for y, p in law.items():
            for z, q in K[y].items():
                nxt[z] = nxt.get(z, F(0)) + p*q
        law = nxt
    return sum((p for y, p in law.items() if y in REGION), F(0))


def receipt():
    result = {"frozen_property": "replete at time 3 (allows exit and re-entry)",
              "persistence": "in replete region at ALL times 0 through L",
              "comparison_design": "v2: whole predeclared replete region; exploratory correction of invalid singleton comparison before infimum evaluation",
              "start": [[1, 1], True], "modes": {}}
    for mode in ("E", "L"):
        K = kernel(mode)
        pi = stationary(K, reachable(K))
        props = {name: replete_at(kernel(mode, *flags)) for name, flags in
                 {"baseline": (False, False), "action": (True, False),
                  "update": (False, True), "joint": (True, True)}.items()}
        result["modes"][mode] = {
            "reachable_states": len(pi),
            "stationary_replete_mass": str(sum(p for y, p in pi.items() if y[1])),
            "stationary_law": {repr(y): str(p) for y, p in pi.items()},
            "killed_persistence": {str(t): str(killed_persistence(K, t)) for t in (0, 1, 2, 3, 5, 20)},
            "property_values": {k: str(v) for k, v in props.items()},
            "singleton_effects": {k: str(abs(v-props["baseline"])) for k, v in props.items() if k != "baseline"}}
        baseline = kernel(mode)
        effects, changes = {}, {}
        for name, flags in {"action": (True, False), "update": (False, True),
                            "joint": (True, True)}.items():
            changed = kernel(mode, *flags)
            changes[name] = {y: replete_at(changed, start=y)-replete_at(baseline, start=y)
                             for y in COMPARISON_STARTS}
            effects[name] = {y: abs(v) for y, v in changes[name].items()}
        result["modes"][mode]["finite_matrix_effects_by_start"] = {
            name: {repr(y): str(v) for y, v in sorted(rows.items())} for name, rows in effects.items()}
        result["modes"][mode]["finite_matrix_effect_infima"] = {
            name: str(min(rows.values())) for name, rows in effects.items()}
        result["modes"][mode]["infimum_starts"] = {
            name: [repr(y) for y, v in sorted(rows.items()) if v == min(rows.values())]
            for name, rows in effects.items()}
        result["modes"][mode]["formal_margin_transport"] = "FiniteOutputs connects original kappa to actual finite-kernel expressions; exact numerical fraction reflection OPEN; corrected-head compilation recorded separately"
        result["modes"][mode]["finite_matrix_direction"] = {
            name: ("strict increase at all nine starts" if all(v > 0 for v in rows.values())
                   else "zero at all nine starts" if all(v == 0 for v in rows.values())
                   else "mixed or nonuniform sign") for name, rows in changes.items()}
    result["application_categories"] = {
        "validity": "exact finite calculations; Lean verification recorded separately",
        "epistemic_mode": "constructed mathematical example",
        "selection": "handover parameter candidate; exploratory comparison-design v2 repair",
        "identification": "structural model stipulated; no empirical identification",
        "statistics": "exact arithmetic; no sampled estimates",
        "provenance": "committed handover candidate; independently checked implementation",
        "substantive_PR_status": "not certified; proposed replete Exact GR fails for both",
        "direction": "reported per frozen intervention and property",
        "uniform_gap_status": "no formal uniform-gap certificate claimed"}
    return result


if __name__ == "__main__":
    import json
    print(json.dumps(receipt(), indent=2, sort_keys=True))
