"""New exact reproductions of the twenty archived specialized review results.

This is newly written reproduction code, not a recovered original review
program.  The archived JSON preserves result names and values but does not
identify the original shell and Gram fixture inputs.  The explicit rational
fixtures below are new choices consistent with the printed formulas.  They
reproduce the saved outputs without reading those outputs during calculation.

Scope: finite real algebra only.  No Lean execution, complete arithmetic
source identity, analytic zero theorem, or independent acceptance is asserted.
The archive-identity check and comparison against its retained records are
the responsibility of the separate reproduction runner.
"""
from __future__ import annotations

from fractions import Fraction as Q


PROVENANCE = {
    "kind": "NEW_SOURCE_CONSISTENT_RECONSTRUCTION",
    "source_section": "sections/C26.tex",
    "source_appendix": "appendices/M_specialized.tex",
    "record": "review/specialized_exact_checks.json",
    "fixture_boundary": (
        "The retained specialized JSON does not specify the shell and Gram input fixtures. "
        "The explicit inputs used here are new source-consistent choices, "
        "not a claim to recover the original review execution."
    ),
    "shell_fixture": {
        "T": [[0, 2], [2, 3]],
        "predecessor": "first coordinate; H=0",
        "nonunit_shell": [0, 2],
        "unit_shell": [0, 1],
        "shift": -1,
    },
    "moment_fixtures": [["1", "2", "3"], ["-2/3", "7/4", "-1/5"], ["0", "0", "0"]],
    "gram_fixture": {
        "x": [1, 2],
        "y": [3, -1],
        "c": 2,
        "positive_background": "P=2*c*y*y^T",
    },
}

SHELL_SOURCE = "sections/C26.tex::eq:C26:secular,eq:C26:derivative; appendices/M_specialized.tex::M:firstbad"
MOMENT_SOURCE = "appendices/M_specialized.tex::eq:M:correction,M:detection"
GRAM_SOURCE = "sections/C26.tex::eq:C26:Gram,C26:gram; appendices/M_specialized.tex::M:gram"


def _dot(x, y):
    if len(x) != len(y):
        raise ValueError("different vector dimensions")
    return sum((a * b for a, b in zip(x, y)), Q(0))


def _matvec(matrix, vector):
    return tuple(_dot(row, vector) for row in matrix)


def _outer(x, y):
    return tuple(tuple(a * b for b in y) for a in x)


def _quadratic(matrix, vector):
    return _dot(vector, _matvec(matrix, vector))


def _poly_value(coefficients, argument):
    """Horner evaluation of ascending-order exact polynomial coefficients."""
    result = Q(0)
    for coefficient in reversed(coefficients):
        result = result * argument + coefficient
    return result


def _poly_derivative(coefficients):
    return tuple(Q(i) * coefficient for i, coefficient in enumerate(coefficients) if i)


def _rational_derivative(numerator, denominator, argument):
    p = _poly_value(numerator, argument)
    q = _poly_value(denominator, argument)
    if not q:
        raise ValueError("rational derivative is undefined at this pole")
    dp = _poly_value(_poly_derivative(numerator), argument)
    dq = _poly_value(_poly_derivative(denominator), argument)
    return (dp * q - p * dq) / (q * q)


def _shell_derivative(shell_scale, shift, *, omit_normalization=False):
    """Differentiate the actual one-core secular quotient, not a saved value.

    W is the first coordinate, c=(0,shell_scale), H=0, and T is symmetric.
    F(lambda)=(theta-lambda)-coupling/(H-lambda).  Expanding its numerator
    gives a quadratic polynomial, whose quotient derivative is evaluated
    independently of the manuscript's resolvent-norm derivative formula.
    """
    scale = Q(shell_scale)
    ell = Q(shift)
    if not scale or ell >= 0:
        raise ValueError("a nonzero shell and a negative shift are required")
    matrix = ((Q(0), Q(2)), (Q(2), Q(3)))
    c = (Q(0), scale)
    tc = _matvec(matrix, c)
    norm_squared = _dot(c, c)
    theta = _dot(tc, c) / norm_squared
    h = matrix[0][0]
    b = tc[0]
    coupling = b * b if omit_normalization else b * b / norm_squared
    numerator = (theta * h - coupling, -(theta + h), Q(1))
    denominator = (h, Q(-1))
    return _rational_derivative(numerator, denominator, ell)


def _correction(moment_values):
    m0, m1, m2 = map(Q, moment_values)
    return {-1: (m1 - m2) / 2, 0: m2 - m0, 1: -(m1 + m2) / 2}


def _moments(coefficients):
    return tuple(
        sum((Q(index) ** degree * value for index, value in coefficients.items()), Q(0))
        for degree in range(3)
    )


def _legalize(coefficients):
    result = dict(coefficients)
    for index, value in _correction(_moments(coefficients)).items():
        result[index] = result.get(index, Q(0)) + value
    return result


def _gram_data():
    x = (Q(1), Q(2))
    y = (Q(3), Q(-1))
    c = Q(2)
    xx, yy, xy = _dot(x, x), _dot(y, y), _dot(x, y)
    gap = xx * yy - xy * xy
    witness = tuple(xx * yi - xy * xi for xi, yi in zip(x, y))
    x_outer, y_outer = _outer(x, x), _outer(y, y)
    signed = tuple(tuple(c * (a - b) for a, b in zip(rx, ry)) for rx, ry in zip(x_outer, y_outer))
    positive = tuple(tuple(2 * c * value for value in row) for row in y_outer)
    masked = tuple(tuple(a + b for a, b in zip(rs, rp)) for rs, rp in zip(signed, positive))
    return x, y, c, gap, witness, signed, positive, masked


def _row(name, value, source, calculation):
    return {"name": name, "actual": str(value), "source": source, "calculation": calculation}


def compute_checks() -> list[dict]:
    """Compute all twenty named results; no archive values enter the arithmetic."""
    rows = [
        _row("nonunit_shell_derivative", _shell_derivative(2, -1), SHELL_SOURCE,
             "Quotient-rule derivative of the secular function for T=((0,2),(2,3)), c=(0,2), lambda=-1."),
        _row("incorrect_unscaled_derivative_would_differ", _shell_derivative(2, -1, omit_normalization=True), SHELL_SOURCE,
             "Deliberately incorrect secular quotient omitting division of the raw coupling square by ||c||^2."),
        _row("unit_shell_derivative", _shell_derivative(1, -1), SHELL_SOURCE,
             "Repeat the same quotient derivative using the unit shell c=(0,1)."),
    ]
    for inputs in ((Q(1), Q(2), Q(3)), (Q(-2, 3), Q(7, 4), Q(-1, 5)), (Q(0), Q(0), Q(0))):
        corrected_moments = _moments(_correction(inputs))
        for degree, value in enumerate(corrected_moments):
            rows.append(_row(
                f"legalization_m{degree}_{inputs[degree]}", value, MOMENT_SOURCE,
                f"Form all three mode corrections from moments {tuple(map(str, inputs))}; sum n^{degree}*(Cu)_n over n=-1,0,1."
            ))
    x, y, c, gap, witness, signed, positive, masked = _gram_data()
    norm_squared = _dot(witness, witness)
    energy = _quadratic(signed, witness)
    gram_rows = [
        ("gram_gap", gap, "Compute ||x||^2*||y||^2-<x,y>^2 for x=(1,2), y=(3,-1)."),
        ("gram_witness", witness, "Form w=||x||^2*y-<x,y>*x from the explicit vectors."),
        ("gram_left_orthogonal", _dot(x, witness), "Compute the direct dot product <x,w>."),
        ("gram_right_pairing", _dot(y, witness), "Compute the direct dot product <y,w>."),
        ("gram_norm", norm_squared, "Compute the direct sum of squares <w,w>."),
        ("gram_energy", energy, "Build B=c*(xx^T-yy^T), c=2, then multiply w^T*B*w."),
        ("gram_normalized_energy", energy / norm_squared, "Divide the directly computed signed energy by the directly computed squared norm."),
        ("gram_masked_energy", _quadratic(masked, witness), "Build the PSD background P=2*c*yy^T and directly multiply w^T*(B+P)*w."),
    ]
    rows.extend(_row(name, value, GRAM_SOURCE, calculation) for name, value, calculation in gram_rows)
    return rows


def negative_controls() -> list[dict]:
    """Separate finite sensitivity checks, not additional archived review rows."""
    x, y, c, gap, witness, signed, positive, masked = _gram_data()
    inputs = (Q(1), Q(2), Q(3))
    wrong_correction = _correction(inputs)
    wrong_correction[1] = -wrong_correction[1]
    original = {-2: Q(1), -1: Q(-4), 0: Q(6), 1: Q(-4), 2: Q(1)}
    # Add the explicit moment right inverse in M:detection to a nonzero legal vector.
    m0, m1, m2 = inputs
    for index, value in {-1: (m2 - m1) / 2, 0: m0 - m2, 1: (m2 + m1) / 2}.items():
        original[index] += value
    legalized = _legalize(original)
    controls = [
        ("omitted_shell_normalization_detected",
         _shell_derivative(2, -1) != _shell_derivative(2, -1, omit_normalization=True),
         SHELL_SOURCE, "The raw-coupling denominator mutation changes the exact secular derivative."),
        ("shell_rescaling_invariance",
         all(_shell_derivative(2, ell) == _shell_derivative(1, ell) for ell in (Q(-1), Q(-2), Q(-3))),
         SHELL_SOURCE, "The normalized secular derivative agrees for unit and nonunit shells at three negative shifts."),
        ("legalization_sign_error_detected",
         _moments(wrong_correction) != tuple(-m for m in inputs),
         MOMENT_SOURCE, "Reversing the +1-mode correction sign fails the required cancellation moments."),
        ("legalization_projection_on_nonzero_fixture",
         _moments(legalized) == (Q(0), Q(0), Q(0)) and _legalize(legalized) == legalized and any(legalized.values()),
         MOMENT_SOURCE, "The explicit moment right inverse plus a nonzero legal five-mode vector becomes legal and is fixed by a second projection."),
        ("positive_background_changes_witness_sign",
         _quadratic(signed, witness) < 0 < _quadratic(masked, witness),
         GRAM_SOURCE, "An admissible PSD background masks the genuine negative signed Gram term on the same witness."),
        ("parallel_gram_vectors_remove_strict_gap",
         _dot(x, x) * _dot(tuple(2 * a for a in x), tuple(2 * a for a in x)) - _dot(x, tuple(2 * a for a in x)) ** 2 == 0,
         GRAM_SOURCE, "A parallel response has zero Gram gap and cannot retain the strict-positive-gap premise."),
    ]
    return [{"name": name, "passed": bool(passed), "source": source, "calculation": calculation}
            for name, passed, source, calculation in controls]
