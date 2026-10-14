"""C11-A research-only exact rational recurrent-class stationary producer.

The trusted mathematical object is a finite, positive-size rational Markov
matrix plus a frozen Boolean descriptor. This Python producer is not a
formally verified implementation and does not certify an external model.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
import json
from pathlib import Path
from typing import Any

FORMAT = "Permansson.C11.stationary-research.v1"
BOUNDARY = ("Exact rational stationary numerical report only. Its independent "
            "checker does not prove Python/JSON correctness, an externally "
            "identified strategic world, original Exact GR or original PR.")
MAX_BYTES = 2_000_000
MAX_STATES = 12
MAX_INPUT_BITS = 256
MAX_VALUE_BITS = 8192


class StationaryError(ValueError):
    pass


class StationaryResourceLimit(StationaryError):
    pass


def strict_pairs(pairs):
    result = {}
    for name, value in pairs:
        if name in result:
            raise StationaryError("duplicate JSON key: " + name)
        result[name] = value
    return result


def _bad_constant(x):
    raise StationaryError("nonfinite JSON value: " + x)


def _bad_float(x):
    raise StationaryError("floating JSON number forbidden: " + x)


def _bounded_int(x):
    if len(x.lstrip("-")) > 2500:
        raise StationaryResourceLimit("JSON integer digit budget")
    try:
        return int(x)
    except ValueError as exc:
        raise StationaryResourceLimit("JSON integer conversion budget") from exc


def strict_loads(raw: bytes):
    if type(raw) is not bytes:
        raise StationaryError("input must be bytes")
    if len(raw) > MAX_BYTES:
        raise StationaryResourceLimit("input byte budget")
    try:
        return json.loads(raw.decode("utf-8"), object_pairs_hook=strict_pairs,
                          parse_int=_bounded_int, parse_float=_bad_float,
                          parse_constant=_bad_constant)
    except (UnicodeError, json.JSONDecodeError, RecursionError) as exc:
        raise StationaryError("invalid JSON") from exc


def canonical_bytes(value):
    return json.dumps(value, sort_keys=True, ensure_ascii=True,
                      allow_nan=False, separators=(",", ":")).encode("ascii")


def fraction(value: Any, *, input_value=False) -> Fraction:
    if type(value) is not str or not value or value.strip() != value:
        raise StationaryError("rational must be a canonical string")
    if len(value) > 2500:
        raise StationaryResourceLimit("rational text budget")
    try:
        q = Fraction(value)
    except (ValueError, ZeroDivisionError, OverflowError) as exc:
        raise StationaryError("invalid rational") from exc
    if str(q) != value:
        raise StationaryError("noncanonical rational")
    max_bits = MAX_INPUT_BITS if input_value else MAX_VALUE_BITS
    if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > max_bits:
        raise StationaryResourceLimit("rational bit budget")
    return q


def bounded(q: Fraction) -> Fraction:
    if max(abs(q.numerator).bit_length(), q.denominator.bit_length()) > MAX_VALUE_BITS:
        raise StationaryResourceLimit("intermediate rational bit budget")
    return q


def normalize_input(obj: Any):
    if type(obj) is not dict or set(obj) != {"n", "matrix", "descriptor"}:
        raise StationaryError("invalid input fields")
    n = obj["n"]
    if type(n) is not int or n < 1:
        raise StationaryError("n must be positive")
    if n > MAX_STATES:
        raise StationaryResourceLimit("state budget")
    h = obj["descriptor"]
    if type(h) is not list or len(h) != n or any(type(x) is not bool for x in h):
        raise StationaryError("descriptor must cover every state as Boolean")
    mat = obj["matrix"]
    if type(mat) is not list or len(mat) != n:
        raise StationaryError("matrix must be square")
    result = []
    for row in mat:
        if type(row) is not list or len(row) != n:
            raise StationaryError("matrix row size")
        vals = tuple(fraction(x, input_value=True) for x in row)
        if any(v < 0 or v > 1 for v in vals) or sum(vals, Fraction(0)) != 1:
            raise StationaryError("row must be exactly stochastic")
        result.append(vals)
    norm = {"n": n, "matrix": [[str(x) for x in row] for row in result],
            "descriptor": list(h)}
    return norm, tuple(result)


def bottom_classes(mat):
    n = len(mat)
    reachable = [[i == j or mat[i][j] > 0 for j in range(n)]
                 for i in range(n)]
    for k in range(n):
        for i in range(n):
            if reachable[i][k]:
                for j in range(n):
                    if reachable[k][j]:
                        reachable[i][j] = True
    unseen = set(range(n))
    classes = []
    while unseen:
        i = min(unseen)
        component = tuple(j for j in sorted(unseen)
                          if reachable[i][j] and reachable[j][i])
        unseen.difference_update(component)
        if all(mat[x][y] == 0 or y in component
               for x in component for y in range(n)):
            classes.append(component)
    return tuple(sorted(classes, key=lambda c: c[0]))


def solve_exact(rows, rhs):
    n = len(rows)
    a = [[bounded(Fraction(x)) for x in row] + [bounded(Fraction(rhs[i]))]
         for i, row in enumerate(rows)]
    for k in range(n):
        pivot = next((i for i in range(k, n) if a[i][k]), None)
        if pivot is None:
            raise StationaryError("singular reference equations; not nonexistence evidence")
        a[k], a[pivot] = a[pivot], a[k]
        d = a[k][k]
        a[k] = [bounded(x / d) for x in a[k]]
        for i in range(n):
            if i == k:
                continue
            f = a[i][k]
            a[i] = [bounded(u - f*v) for u, v in zip(a[i], a[k])]
    return tuple(row[-1] for row in a)


def stationary_vector(mat, cls):
    m, n = len(cls), len(mat)
    a = [[Fraction(int(i == j)) - mat[cls[j]][cls[i]]
          for j in range(m)] for i in range(m - 1)]
    a.append([Fraction(1)] * m)
    v = solve_exact(a, [Fraction(0)] * (m - 1) + [Fraction(1)])
    out = [Fraction(0)] * n
    for x, weight in zip(cls, v):
        out[x] = bounded(weight)
    if (any(x < 0 for x in out)
            or sum(out, Fraction(0)) != 1
            or any(sum((out[x] * mat[x][y] for x in range(n)),
                       Fraction(0)) != out[y] for y in range(n))):
        raise StationaryError("reference equations did not produce an accepted vector")
    return tuple(out)


def execute(input_value):
    norm, mat = normalize_input(input_value)
    classes = []
    for cls in bottom_classes(mat):
        vec = stationary_vector(mat, cls)
        share = bounded(sum((vec[i] for i, v in enumerate(norm["descriptor"]) if v),
                            Fraction(0)))
        classes.append({"states": list(cls), "stationary": [str(x) for x in vec],
                        "true_share": str(share)})
    return {"format": FORMAT,
            "normalized_input": norm,
            "input_sha256": sha256(canonical_bytes(norm)).hexdigest(),
            "classes": classes, "claim_boundary": BOUNDARY}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", type=Path)
    parser.add_argument("-o", "--output", type=Path, required=True)
    args = parser.parse_args(argv)
    request = strict_loads(args.input.read_bytes())
    result = execute(request)
    from c11_verify_stationary import verify_report
    verify_report(result)
    args.output.write_bytes(canonical_bytes(result) + b"\n")
    print("C11 exact numerical stationary report verified: "
          + result["input_sha256"])


if __name__ == "__main__":
    main()
