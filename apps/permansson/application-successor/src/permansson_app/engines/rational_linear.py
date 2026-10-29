"""Small exact-rational linear algebra for bounded finite Markov problems.

This module is only a proposal/calculation substrate. Independently validating
receipts never assumes that successful elimination proves model correspondence.
"""
from __future__ import annotations
from fractions import Fraction
from ..errors import AppError


def solve_unique(matrix, right):
    """Return unique solution over Q, or fail closed for singular/non-square input."""
    n = len(matrix)
    if len(right) != n or any(len(row) != n for row in matrix):
        raise AppError('LINEAR_DIMENSION', 'exact linear system has inconsistent dimensions')
    if not n:
        return ()
    rows = [[Fraction(value) for value in row] + [Fraction(right[i])]
            for i, row in enumerate(matrix)]
    for column in range(n):
        pivot = next((r for r in range(column, n) if rows[r][column] != 0), None)
        if pivot is None:
            raise AppError('LINEAR_SINGULAR', 'system lacks a unique exact solution')
        rows[column], rows[pivot] = rows[pivot], rows[column]
        factor = rows[column][column]
        rows[column] = [v / factor for v in rows[column]]
        for r in range(n):
            if r == column or rows[r][column] == 0:
                continue
            multiple = rows[r][column]
            rows[r] = [v - multiple * w for v, w in zip(rows[r], rows[column])]
    solution = tuple(row[-1] for row in rows)
    if any(sum(Fraction(a) * x for a, x in zip(row, solution)) != Fraction(b)
           for row, b in zip(matrix, right)):
        raise AppError('LINEAR_ERROR', 'computed solution fails original equations')
    return solution
