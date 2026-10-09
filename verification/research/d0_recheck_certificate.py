"""D0-F independent exact FORWARD-flow rechecker for untrusted JSON records.

Unlike the generator's backward finite-horizon recursion, this implementation
propagates live state probability mass and accumulates first goal hits.
Consistency with supplied data is not source authentication or a Lean proof.
"""
from __future__ import annotations

from dataclasses import dataclass
from fractions import Fraction
import re
import sys
from pathlib import Path

from d0_certificate import (
    CertificateError, CertificateResourceLimit, FAMILY, MAX_VALUE_BITS,
    SCHEMA, SCOPE, _check_budget, _decode_problem_for_solver,
    _integer, canonical_bytes, fraction_pair, normalize_problem, parse_json_strict,
    problem_digest, read_pair,
)

GOOD = "VALID"
BAD = "INVALID"
LIMIT = "RESOURCE_LIMIT"


@dataclass(frozen=True)
class VerificationResult:
    status: str
    reason: str
    problem_sha256: str | None = None


def _keys(d, expected):
    if type(d) is not dict or set(d) != set(expected):
        raise CertificateError("unexpected/missing fields: " + ",".join(expected))


def _validate_problem(problem):
    _keys(problem, ("family", "dimension", "baseline_rows", "menu",
                    "initial", "goal", "forbidden", "horizon"))
    if problem["family"] != FAMILY:
        raise CertificateError("unexpected research family")
    n = _integer(problem["dimension"], "dimension", 1, 12)
    _integer(problem["initial"], "initial", 0, n-1)
    _integer(problem["horizon"], "horizon", 0, 128)
    if type(problem["menu"]) is not list:
        raise CertificateError("invalid menu shape")
    _check_budget(n, problem["horizon"], len(problem["menu"]))
    if type(problem["baseline_rows"]) is not list:
        raise CertificateError("invalid baseline matrix shape")
    def decode_matrix(rows):
        if type(rows) is not list:
            raise CertificateError("invalid matrix shape")
        return tuple(tuple(read_pair(v, input_entry=True) for v in row)
                     if type(row) is list else _raise("invalid matrix row")
                     for row in rows)
    baseline = decode_matrix(problem["baseline_rows"])
    menu = []
    for item in problem["menu"]:
        _keys(item, ("label", "rows"))
        menu.append((item["label"], decode_matrix(item["rows"])))
    if type(problem["goal"]) is not list or type(problem["forbidden"]) is not list:
        raise CertificateError("invalid target set shape")
    canonical = normalize_problem(menu, baseline, problem["initial"],
                                  problem["goal"], problem["forbidden"],
                                  problem["horizon"])
    if canonical != problem:
        raise CertificateError("noncanonical or changed normalized problem")
    return menu


def _raise(reason):
    raise CertificateError(reason)


def _bound_forward_mass(value):
    """Reject oversized exact fractions, including probability still in flight.

    An unreachable goal can leave won=0 while active denominators grow
    exponentially; the resource guard must cover each intermediate mass.
    """
    if max(abs(value.numerator).bit_length(), value.denominator.bit_length()) > MAX_VALUE_BITS:
        raise CertificateResourceLimit("forward rational bit limit")


def forward_first_hit_value(matrix, initial, goal, forbidden, horizon):
    """Independent O(T*n²) exact propagation, including time-zero semantics."""
    n = len(matrix)
    goals, dangers = set(goal), set(forbidden)
    won = Fraction(1) if initial in goals else Fraction(0)
    active = [Fraction(0)] * n
    if initial not in goals and initial not in dangers:
        active[initial] = Fraction(1)
    for _ in range(horizon):
        after = [Fraction(0)] * n
        for y, mass in enumerate(active):
            if not mass:
                continue
            for z, q in enumerate(matrix[y]):
                if not q:
                    continue
                moved = mass * q
                _bound_forward_mass(moved)
                if z in goals:
                    won += moved
                    _bound_forward_mass(won)
                elif z not in dangers:
                    after[z] += moved
                    _bound_forward_mass(after[z])
        active = after
        if all(not mass for mass in active):
            break
    return won


def _verify(raw, expected_problem_sha256=None):
    rec = parse_json_strict(raw)
    _keys(rec, ("schema", "scope", "problem", "problem_sha256", "calculation"))
    if rec["schema"] != SCHEMA or rec["scope"] != SCOPE:
        raise CertificateError("unsupported schema or forged scope")
    menu = _validate_problem(rec["problem"])
    digest = problem_digest(rec["problem"])
    if type(rec["problem_sha256"]) is not str or rec["problem_sha256"] != digest:
        raise CertificateError("problem digest mismatch")
    if expected_problem_sha256 is not None:
        if (type(expected_problem_sha256) is not str or
                re.fullmatch(r"[0-9a-f]{64}", expected_problem_sha256) is None):
            raise CertificateError("malformed external expected digest")
        if digest != expected_problem_sha256:
            raise CertificateError("problem differs from externally expected input")
    calc = rec["calculation"]
    _keys(calc, ("values", "selected", "value"))
    values = calc["values"]
    if type(values) is not list or len(values) != len(menu):
        raise CertificateError("missing or extra candidate results")
    initial, goal, forbidden, horizon = (
        rec["problem"][k] for k in ("initial", "goal", "forbidden", "horizon")
    )
    expected = []
    for reported, (label, matrix) in zip(values, menu):
        _keys(reported, ("label", "value"))
        if type(reported["label"]) is not str or reported["label"] != label:
            raise CertificateError("candidate results reordered or renamed")
        actual = forward_first_hit_value(matrix, initial, goal, forbidden, horizon)
        if read_pair(reported["value"]) != actual:
            raise CertificateError("inexact candidate value")
        expected.append((label, actual))
    best = max(expected, key=lambda item: item[1])  # first-listed ties
    if type(calc["selected"]) is not str or calc["selected"] != best[0]:
        raise CertificateError("wrong candidate selected")
    if read_pair(calc["value"]) != best[1]:
        raise CertificateError("wrong winning value")
    return digest


def check_certificate(raw, expected_problem_sha256=None):
    """Tri-state verification: INVALID != unsupported resource-limit."""
    try:
        digest = _verify(raw, expected_problem_sha256)
        return VerificationResult(GOOD, "independent exact forward evaluation agrees", digest)
    except CertificateResourceLimit as exc:
        return VerificationResult(LIMIT, str(exc))
    except (CertificateError, TypeError, ValueError, ZeroDivisionError,
            OverflowError) as exc:
        return VerificationResult(BAD, str(exc))


def main(argv=None):
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("certificate", help="canonical JSON file")
    parser.add_argument("--expected-problem-sha256", default=None,
                        help="trusted expected digest supplied independently of certificate")
    args = parser.parse_args(argv)
    path = Path(args.certificate)
    try:
        if path.stat().st_size > 2_000_000:
            result = VerificationResult(LIMIT, "certificate byte limit")
        else:
            result = check_certificate(path.read_bytes(), args.expected_problem_sha256)
    except (OSError, ValueError) as exc:
        result = VerificationResult(BAD, str(exc))
    print(result.status + ": " + result.reason)
    return 0 if result.status == GOOD else (2 if result.status == LIMIT else 1)


if __name__ == "__main__":
    sys.exit(main())
