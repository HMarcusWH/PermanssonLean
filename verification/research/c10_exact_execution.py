"""C10 finite-rational eventual-Boolean constitutive-margin reference executor.

An independent exact-rational *numerical* implementation. Its output is not
by itself a Lean certificate, a typed strategic-world realization of an
external game, an Exact-GR proof, or empirical causal identification.

The frozen input has one stationary matrix per menu choice and one common
Boolean descriptor and B1. Bounded graph reachability is exact (>0). Class
absorption is solved over fractions; no epsilon or horizon truncation.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
from hashlib import sha256
import json
from dataclasses import dataclass
from typing import Any

Q0, Q1 = Fraction(0), Fraction(1)


class InputError(ValueError):
    pass


def _check_keys(obj: dict, required: set[str], optional: set[str] = frozenset()):
    if set(obj) - (required | optional) or required - set(obj):
        raise InputError(f"unexpected/missing keys: {sorted(set(obj) ^ required)}")


def exact_fraction(v: Any) -> Fraction:
    """Require canonical finite rational string; never admit floats/decimals."""
    if not isinstance(v, str) or not v or v.strip() != v:
        raise InputError("probabilities must be canonical rational strings")
    try:
        q = Fraction(v)
    except (ValueError, ZeroDivisionError) as e:
        raise InputError("invalid rational") from e
    if str(q) != v:
        raise InputError(f"noncanonical rational: {v}")
    return q


def format_fraction(q: Fraction) -> str:
    return str(q)


def checked_matrix(raw: Any, n: int) -> tuple[tuple[Fraction, ...], ...]:
    if not isinstance(raw, list) or len(raw) != n:
        raise InputError("matrix not n rows")
    out = []
    for row in raw:
        if not isinstance(row, list) or len(row) != n:
            raise InputError("matrix not square")
        parsed = tuple(exact_fraction(q) for q in row)
        if any(q < Q0 or q > Q1 for q in parsed) or sum(parsed, Q0) != Q1:
            raise InputError("row must be exactly stochastic")
        out.append(parsed)
    return tuple(out)


@dataclass(frozen=True)
class FrozenInput:
    n: int
    baseline: tuple[tuple[Fraction, ...], ...]
    descriptor: tuple[bool, ...]
    comparison: tuple[int, ...]
    menu: tuple[tuple[str, tuple[tuple[Fraction, ...], ...]], ...]

    def canonical(self) -> dict:
        def encode_matrix(m):
            return [[format_fraction(v) for v in row] for row in m]
        return {"n": self.n, "baseline": encode_matrix(self.baseline),
                "descriptor": list(self.descriptor),
                "comparison": list(self.comparison),
                "menu": [{"id": label, "matrix": encode_matrix(matrix)}
                         for label, matrix in self.menu]}


def check_input(obj: Any) -> FrozenInput:
    if not isinstance(obj, dict):
        raise InputError("input must be object")
    _check_keys(obj, {"n", "baseline", "descriptor", "comparison", "menu"})
    n = obj["n"]
    if type(n) is not int or n <= 0:
        raise InputError("n must be positive integer")
    baseline = checked_matrix(obj["baseline"], n)
    descriptor = obj["descriptor"]
    if not isinstance(descriptor, list) or len(descriptor) != n or any(type(b) is not bool for b in descriptor):
        raise InputError("descriptor must supply exactly n booleans")
    br = obj["comparison"]
    if not isinstance(br, list) or not br:
        raise InputError("comparison must be nonempty list")
    if any(type(x) is not int or x < 0 or x >= n for x in br):
        raise InputError("comparison state out of range")
    comparison = tuple(sorted(set(br)))
    menu_raw = obj["menu"]
    if not isinstance(menu_raw, list) or not menu_raw:
        raise InputError("frozen menu must be nonempty")
    normalized = {}
    for item in menu_raw:
        if not isinstance(item, dict):
            raise InputError("menu member must be object")
        _check_keys(item, {"id", "matrix"})
        label = item["id"]
        if not isinstance(label, str) or not label or label.strip() != label:
            raise InputError("member ID must be nonempty string")
        matrix = checked_matrix(item["matrix"], n)
        if label in normalized and matrix != normalized[label]:
            raise InputError("conflicting duplicate menu ID")
        normalized[label] = matrix
    return FrozenInput(n, baseline, tuple(descriptor), comparison, tuple(normalized.items()))


def transitive_reach(matrix: tuple[tuple[Fraction, ...], ...]) -> tuple[tuple[bool, ...], ...]:
    """Reflexive transitive closure using exact positive-edge Floyd-Warshall."""
    n = len(matrix)
    reach = [[i == j or matrix[i][j] > Q0 for j in range(n)] for i in range(n)]
    for k in range(n):
        for i in range(n):
            if reach[i][k]:
                for j in range(n):
                    if reach[k][j]:
                        reach[i][j] = True
    return tuple(tuple(row) for row in reach)


def bottom_classes(matrix: tuple[tuple[Fraction, ...], ...]) -> tuple[tuple[int, ...], ...]:
    n = len(matrix)
    reach = transitive_reach(matrix)
    unseen = set(range(n))
    classes = []
    while unseen:
        i = min(unseen)
        comp = tuple(j for j in range(n) if reach[i][j] and reach[j][i])
        unseen.difference_update(comp)
        if all(matrix[k][j] == 0 or j in comp for k in comp for j in range(n)):
            classes.append(comp)
    assert classes
    return tuple(sorted(classes, key=lambda x: x[0]))


def solve(a: tuple[tuple[Fraction,...],...], rhs: tuple[Fraction,...]) -> tuple[Fraction,...]:
    """Exact Gaussian elimination with pivoting on nonsingular matrices."""
    n = len(rhs)
    if len(a) != n or any(len(row) != n for row in a):
        raise ValueError("invalid linear system")
    augmented = [list(a[i]) + [rhs[i]] for i in range(n)]
    for k in range(n):
        pivot_row = next((j for j in range(k,n) if augmented[j][k] != Q0), None)
        if pivot_row is None:
            raise ArithmeticError("Dirichlet matrix unexpectedly singular")
        augmented[pivot_row], augmented[k] = augmented[k], augmented[pivot_row]
        pivot = augmented[k][k]
        augmented[k] = [x / pivot for x in augmented[k]]
        for j in range(n):
            if j != k:
                factor = augmented[j][k]
                if factor:
                    augmented[j] = [augmented[j][z]-factor*augmented[k][z] for z in range(n+1)]
    return tuple(row[n] for row in augmented)


def absorption(matrix: tuple[tuple[Fraction,...],...]):
    classes = bottom_classes(matrix)
    n = len(matrix)
    recurrent = {x for cls in classes for x in cls}
    transient = tuple(i for i in range(n) if i not in recurrent)
    a = tuple(tuple((Q1 if i == j else Q0)-matrix[i][j] for j in transient) for i in transient)
    weights = []
    for cls in classes:
        rhs = tuple(sum((matrix[i][z] for z in cls), Q0) for i in transient)
        solved = solve(a, rhs)
        tmap = dict(zip(transient, solved))
        w = tuple(Q1 if i in cls else Q0 if i in recurrent else tmap[i] for i in range(n))
        weights.append(w)
    if not all(Q0 <= w[i] <= Q1 for w in weights for i in range(n)):
        raise ArithmeticError("absorption outside [0,1]")
    if not all(sum((w[i] for w in weights), Q0) == Q1 for i in range(n)):
        raise ArithmeticError("class absorption probabilities do not partition one")
    return classes, tuple(weights)


def class_values(matrix, descriptor: tuple[bool,...]) -> dict:
    classes, weights = absorption(matrix)
    good = tuple(all(descriptor[i] for i in c) for c in classes)
    probs = tuple(sum((weights[j][i] for j, g in enumerate(good) if g), Q0) for i in range(len(matrix)))
    return {"classes": [list(c) for c in classes], "absorption": [[str(v) for v in w] for w in weights],
            "good": list(good), "event": [str(v) for v in probs]}


def canonical_bytes(obj):
    return json.dumps(obj, ensure_ascii=False, sort_keys=True, separators=(',',':')).encode('utf-8')


def execute(valid: FrozenInput) -> dict:
    normalized = valid.canonical()
    base = class_values(valid.baseline, valid.descriptor)
    basevals = tuple(Fraction(v) for v in base["event"])
    items = []
    for label, matrix in valid.menu:
        res = class_values(matrix, valid.descriptor)
        effects = tuple(abs(basevals[i] - Fraction(res["event"][i])) for i in valid.comparison)
        val = min(effects)
        worst = min(i for i, d in zip(valid.comparison, effects) if d == val)
        items.append({"id":label, "geometry":res,
                      "effects": [str(v) for v in effects], "margin":str(val),
                      "worst_start": worst})
    optimum = max(Fraction(x["margin"]) for x in items)
    ties = [x["id"] for x in items if Fraction(x["margin"]) == optimum]
    status = "NUMERIC_ALL_LISTED_MARGINS_ZERO" if optimum == Q0 else "NUMERIC_POSITIVE_BASELINE_UNVERIFIED"
    return {"format":"Permansson.C10.rational-margin.v1", "normalized_input": normalized,
            "input_sha256":sha256(canonical_bytes(normalized)).hexdigest(),
            "baseline":base,"members":items,"optimum":str(optimum),
            "ties":ties,"selected":ties[0], "numerical_status":status,
            "claim_boundary":"Exact rational numerical result only; original typed equality and any positive PR certification require separate Lean theorems."}


def strict_object(pairs):
    """Reject duplicate JSON object keys before normalization/proof binding."""
    result = {}
    for key, value in pairs:
        if key in result:
            raise InputError(f"duplicate JSON key: {key}")
        result[key] = value
    return result


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',help='strict rational input JSON')
    parser.add_argument('-o','--output',required=True,help='output receipt JSON')
    args=parser.parse_args(argv)
    with open(args.input,encoding='utf-8') as f:
        data=json.load(f, parse_float=lambda _: (_ for _ in ()).throw(InputError('floating JSON number')), object_pairs_hook=strict_object)
    receipt=execute(check_input(data))
    with open(args.output,'w',encoding='utf-8') as f:
        json.dump(receipt,f,sort_keys=True,indent=2,ensure_ascii=False)
        f.write('\n')
    print(f"C10 reference arithmetic: {len(receipt['members'])} listed; optimum {receipt['optimum']} at {receipt['selected']} (not a Lean proof)")

if __name__ == '__main__':
    main()