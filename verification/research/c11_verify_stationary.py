"""Independent C11 stationary report checker: DFS classes and exact equations.

Intentionally does not invoke the producer's bottomClasses, linear solver,
matrix inversion or stationary_vector routine. Shared strict parsing and
normalization are an explicitly nonformal Python/JSON trust boundary.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import re

from c11_stationary_execution import (BOUNDARY, FORMAT, StationaryError,
    canonical_bytes, fraction, normalize_input, strict_loads)


def require(condition, message):
    if not condition:
        raise StationaryError(message)


def dfs(mat, start):
    reached = {start}
    pending = [start]
    while pending:
        x = pending.pop()
        for y, value in enumerate(mat[x]):
            if value > 0 and y not in reached:
                reached.add(y)
                pending.append(y)
    return reached


def independent_classes(mat):
    n = len(mat)
    reach = [dfs(mat, i) for i in range(n)]
    unseen = set(range(n))
    classes = []
    while unseen:
        x = min(unseen)
        component = set(y for y in unseen if y in reach[x] and x in reach[y])
        unseen -= component
        if all(mat[y][z] == 0 or z in component
               for y in component for z in range(n)):
            classes.append(tuple(sorted(component)))
    return tuple(sorted(classes, key=lambda c: c[0]))


def verify_report(obj):
    require(type(obj) is dict and set(obj) == {
        "format", "normalized_input", "input_sha256", "classes", "claim_boundary"},
        "invalid complete report fields")
    require(obj["format"] == FORMAT, "incorrect stationary schema")
    require(obj["claim_boundary"] == BOUNDARY, "changed scope boundary")
    norm, mat = normalize_input(obj["normalized_input"])
    require(obj["normalized_input"] == norm, "noncanonical input")
    digest = sha256(canonical_bytes(norm)).hexdigest()
    require(type(obj["input_sha256"]) is str
            and re.fullmatch("[0-9a-f]{64}", obj["input_sha256"])
            and digest == obj["input_sha256"], "normalized input hash mismatch")
    actual = independent_classes(mat)
    classes = obj["classes"]
    require(type(classes) is list and len(classes) == len(actual),
            "incomplete or duplicated class table")
    n = norm["n"]
    for reported, cls in zip(classes, actual):
        require(type(reported) is dict and set(reported) ==
                {"states", "stationary", "true_share"}, "wrong class fields")
        require(reported["states"] == list(cls), "wrong/missing/extra or reordered class")
        v = reported["stationary"]
        require(type(v) is list and len(v) == n, "incomplete stationary vector")
        values = [fraction(x) for x in v]
        require(all(0 <= p <= 1 for p in values), "negative or excessive probability")
        require(sum(values, Fraction(0)) == 1, "stationary unit-mass failure")
        require(all(values[i] == 0 for i in range(n) if i not in cls),
                "nonzero off-class mass")
        for y in range(n):
            actual_balance = sum((values[x] * mat[x][y] for x in range(n)), Fraction(0))
            require(actual_balance == values[y], "full stationary balance failure")
        actual_share = sum((values[x] for x in range(n) if norm["descriptor"][x]),
                           Fraction(0))
        require(fraction(reported["true_share"]) == actual_share,
                "incorrect frozen observed stationary share")
    return True


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("report", type=Path)
    args = parser.parse_args(argv)
    value = strict_loads(args.report.read_bytes())
    verify_report(value)
    print("C11 independent exact stationary verification PASS: "
          + value["input_sha256"])


if __name__ == "__main__":
    main()
