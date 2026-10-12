"""Lane C4 exact-rational adversaries for the typed six-state precision proof.

This module is an independent finite arithmetic/negative-controls suite.
It is NOT a proof of the Lean theorem, true infinite-path identification,
or mathematical existence/uniqueness outside the frozen small models.
The expected six-state matrix is separately written down, not compared
with itself. All arithmetic uses Python's exact Fraction objects.
"""

from fractions import Fraction as F
import unittest

ZERO = F(0)
ONE = F(1)
HALF = F(1, 2)

# Independently frozen source-reference matrix, in (t,u,a0,a1,b0,b1) order.
EXPECTED = (
    (ZERO, ONE, ZERO, ZERO, ZERO, ZERO),
    (ZERO, HALF, F(1, 6), ZERO, F(1, 3), ZERO),
    (ZERO, ZERO, ZERO, ONE, ZERO, ZERO),
    (ZERO, ZERO, ONE, ZERO, ZERO, ZERO),
    (ZERO, ZERO, ZERO, ZERO, HALF, HALF),
    (ZERO, ZERO, ZERO, ZERO, F(1, 4), F(3, 4)),
)
A = frozenset((2, 3))
B = frozenset((4, 5))
PI_A = (ZERO, ZERO, HALF, HALF, ZERO, ZERO)
PI_B = (ZERO, ZERO, ZERO, ZERO, F(1, 3), F(2, 3))


def source_transition(i, j):
    """Independently coded reference to the six-state Lean transition cases."""
    if i == 0:
        return ONE if j == 1 else ZERO
    if i == 1:
        if j == 1:
            return HALF
        if j == 2:
            return F(1, 6)
        return F(1, 3) if j == 4 else ZERO
    if i == 2:
        return ONE if j == 3 else ZERO
    if i == 3:
        return ONE if j == 2 else ZERO
    if i == 4:
        return HALF if j in (4, 5) else ZERO
    return F(1, 4) if j == 4 else F(3, 4) if j == 5 else ZERO


def validate_matrix(matrix, n=6):
    if len(matrix) != n:
        raise ValueError("wrong number of transition rows")
    for row in matrix:
        if len(row) != n:
            raise ValueError("wrong number of columns")
        if any(not isinstance(x, F) for x in row):
            raise ValueError("row entries must be exact Fractions")
        if any(x < ZERO or x > ONE for x in row):
            raise ValueError("transition mass outside [0,1]")
        if sum(row, ZERO) != ONE:
            raise ValueError("stochastic row is not normalized")
    return matrix


def step(row, matrix):
    return tuple(sum((row[i] * matrix[i][j] for i in range(len(matrix))), ZERO)
                 for j in range(len(matrix)))


def unit(n, i):
    return tuple(ONE if j == i else ZERO for j in range(n))


def stationary(row, matrix):
    return step(row, matrix) == row


def support(row):
    return frozenset(i for i, value in enumerate(row) if value)


def marginal_sequence(start, matrix, horizon):
    result = []
    v = start
    for _ in range(horizon + 1):
        result.append(v)
        v = step(v, matrix)
    return result


def fraction_occupation(path, n_states):
    if not path:
        raise ValueError("occupation horizon must be positive")
    return tuple(F(sum(i == j for i in path), len(path))
                 for j in range(n_states))


def graph_reachable(matrix, start, goal):
    pending = [start]
    visited = {start}
    while pending:
        i = pending.pop()
        if i == goal:
            return True
        for j, probability in enumerate(matrix[i]):
            if probability > ZERO and j not in visited:
                pending.append(j)
                visited.add(j)
    return False


def tiny_branch_matrix(epsilon, holding=F(2, 3)):
    """Frozen 3-state q/A/B chain with P_q(eventually A)=epsilon."""
    if not isinstance(epsilon, F) or not isinstance(holding, F):
        raise ValueError("epsilon and holding must be exact Fractions")
    if not ZERO <= epsilon <= ONE or not ZERO <= holding < ONE:
        raise ValueError("parameters outside permitted ranges")
    matrix = (
        (holding, (ONE - holding) * epsilon,
         (ONE - holding) * (ONE - epsilon)),
        (ZERO, ONE, ZERO),
        (ZERO, ZERO, ONE),
    )
    return validate_matrix(matrix, 3)


def exact_absorb_A(matrix):
    """Closed-form first-step solution for this *specified* q/A/B chain."""
    validate_matrix(matrix, 3)
    # Verify the intended two-state absorbing subclass, fail closed.
    if matrix[1] != (ZERO, ONE, ZERO) or matrix[2] != (ZERO, ZERO, ONE):
        raise ValueError("not the declared absorbing q/A/B system")
    r, p, _ = matrix[0]
    if r == ONE:
        raise ValueError("q never leaves")
    return p / (ONE - r)


class ExactSixStateC4(unittest.TestCase):
    def test_01_independent_36_entry_matrix_and_stochastic_rows(self):
        actual = tuple(tuple(source_transition(i, j) for j in range(6))
                       for i in range(6))
        self.assertEqual(validate_matrix(actual), EXPECTED)
        for i in range(6):
            for j in range(6):
                self.assertEqual(actual[i][j], EXPECTED[i][j],
                                 msg=f"wrong source atom ({i},{j})")

    def test_02_all_A_coordinates(self):
        self.assertEqual(PI_A, (0, 0, HALF, HALF, 0, 0))
        self.assertEqual(support(PI_A), A)
        self.assertEqual(sum(PI_A, ZERO), ONE)

    def test_03_all_B_coordinates(self):
        self.assertEqual(PI_B, (0, 0, 0, 0, F(1, 3), F(2, 3)))
        self.assertEqual(support(PI_B), B)
        self.assertEqual(sum(PI_B, ZERO), ONE)

    def test_04_both_exact_stationary_whole_rows(self):
        self.assertTrue(stationary(PI_A, EXPECTED))
        self.assertTrue(stationary(PI_B, EXPECTED))
        self.assertEqual(support(PI_A) & support(PI_B), frozenset())

    def test_05_a0_all_powers_zero_through_40(self):
        seq = marginal_sequence(unit(6, 2), EXPECTED, 40)
        for n, law in enumerate(seq):
            self.assertEqual(law, unit(6, 2 if n % 2 == 0 else 3))

    def test_06_a1_reverses_the_parity(self):
        seq = marginal_sequence(unit(6, 3), EXPECTED, 40)
        for n, law in enumerate(seq):
            self.assertEqual(law, unit(6, 3 if n % 2 == 0 else 2))

    def test_07_exact_empirical_counts_at_both_parities(self):
        for N in (1, 2, 3, 4, 5, 31, 40, 41, 400, 401):
            deterministic_path = [2 if k % 2 == 0 else 3 for k in range(N)]
            expected = tuple(
                F((N + 1) // 2, N) if j == 2
                else F(N // 2, N) if j == 3 else ZERO
                for j in range(6)
            )
            occupation = fraction_occupation(deterministic_path, 6)
            self.assertEqual(occupation, expected)
            self.assertLessEqual(abs(occupation[2] - HALF), F(1, N))

    def test_08_stationary_initial_law_has_constant_marginals(self):
        seq = marginal_sequence(PI_A, EXPECTED, 40)
        self.assertEqual(seq, [PI_A] * 41)

    def test_09_stochastic_mutations_break_parity_or_stationarity(self):
        altered_A = [list(row) for row in EXPECTED]
        altered_A[2][2] = F(1, 4)
        altered_A[2][3] = F(3, 4)
        altered_A = validate_matrix(tuple(tuple(x) for x in altered_A))
        self.assertNotEqual(step(unit(6, 2), altered_A), unit(6, 3))
        self.assertFalse(stationary(PI_A, altered_A))
        altered_B = [list(row) for row in EXPECTED]
        altered_B[4][4] = F(3, 4)
        altered_B[4][5] = F(1, 4)
        altered_B = validate_matrix(tuple(tuple(x) for x in altered_B))
        self.assertFalse(stationary(PI_B, altered_B))

    def test_10_random_class_law_is_not_a_pathwise_barycenter(self):
        weights = (F(1, 3), F(2, 3))
        barycenter = tuple(weights[0] * a + weights[1] * b
                           for a, b in zip(PI_A, PI_B))
        self.assertEqual(barycenter,
                         (ZERO, ZERO, F(1, 6), F(1, 6), F(2, 9), F(4, 9)))
        self.assertNotEqual(barycenter, PI_A)
        self.assertNotEqual(barycenter, PI_B)
        self.assertEqual(sum(weights, ZERO), ONE)

    def test_11_arbitrarily_tiny_actual_positive_absorption_weight(self):
        for eps in (F(1, 10), F(1, 10**6), F(1, 10**35)):
            m = tiny_branch_matrix(eps)
            self.assertTrue(graph_reachable(m, 0, 1))
            self.assertEqual(exact_absorb_A(m), eps)
            self.assertEqual(m[0][1], F(1, 3) * eps)
            self.assertTrue(stationary(unit(3, 1), m))
        m0 = tiny_branch_matrix(ZERO)
        self.assertFalse(graph_reachable(m0, 0, 1))
        self.assertEqual(exact_absorb_A(m0), ZERO)

    def test_12_invalid_fractions_rows_and_ranges_raise(self):
        for invalid in (F(-1, 10), F(11, 10), "0.1", 0.1):
            with self.assertRaises(ValueError):
                tiny_branch_matrix(invalid)
        for invalid_holding in (ZERO - F(1, 4), ONE, F(5, 4)):
            with self.assertRaises(ValueError):
                tiny_branch_matrix(F(1, 10), invalid_holding)
        with self.assertRaises(ValueError):
            validate_matrix(((F(1), F(0)),))
        broken = [list(row) for row in EXPECTED]
        broken[0][1] = F(3, 4)
        with self.assertRaises(ValueError):
            validate_matrix(tuple(tuple(x) for x in broken))
        broken = [list(row) for row in EXPECTED]
        broken[0][1] = F(3, 2)
        with self.assertRaises(ValueError):
            validate_matrix(tuple(tuple(x) for x in broken))
        broken = [list(row) for row in EXPECTED]
        broken[0][1] = 1.0
        with self.assertRaises(ValueError):
            validate_matrix(tuple(tuple(x) for x in broken))


if __name__ == "__main__":
    unittest.main()
