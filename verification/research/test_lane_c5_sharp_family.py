"""C5 independent exact-rational adversaries for sharp observed-limit families.

All arithmetic is fractions.Fraction; no simulation, sampling cutoff,
floating-point stationarity assertion or post-hoc member padding.
These are computational regression controls, NOT Lean theorem proofs.
"""
import unittest
from fractions import Fraction as F


ZERO, ONE = F(0), F(1)

# Literal matrix, independently transcribed from the frozen six-state model.
M = (
    (ZERO, ONE, ZERO, ZERO, ZERO, ZERO),
    (ZERO, F(1, 2), F(1, 6), ZERO, F(1, 3), ZERO),
    (ZERO, ZERO, ZERO, ONE, ZERO, ZERO),
    (ZERO, ZERO, ONE, ZERO, ZERO, ZERO),
    (ZERO, ZERO, ZERO, ZERO, F(1, 2), F(1, 2)),
    (ZERO, ZERO, ZERO, ZERO, F(1, 4), F(3, 4)),
)
CLASSES = ((2, 3), (4, 5))


def exact_matrix(a):
    """Fail closed: accept only stochastic square Fraction matrices."""
    n = len(a)
    if n < 1 or any(len(row) != n for row in a):
        raise ValueError("non-square or empty")
    if any(not isinstance(x, F) or x < ZERO or x > ONE
           for row in a for x in row):
        raise ValueError("unsafe entry")
    if any(sum(row, ZERO) != ONE for row in a):
        raise ValueError("row does not sum to one")
    return tuple(tuple(row) for row in a)


def solve(a, b):
    """Independent rational Gauss-Jordan: unique solution only."""
    n = len(b)
    if len(a) != n or any(len(row) != n for row in a):
        raise ValueError("wrong dimensions")
    q = [list(a[i]) + [b[i]] for i in range(n)]
    for col in range(n):
        pivot = next((r for r in range(col, n) if q[r][col] != ZERO), None)
        if pivot is None:
            raise ValueError("singular")
        q[col], q[pivot] = q[pivot], q[col]
        scale = q[col][col]
        q[col] = [v / scale for v in q[col]]
        for row in range(n):
            if row == col:
                continue
            scale = q[row][col]
            q[row] = [q[row][k] - scale*q[col][k] for k in range(n+1)]
    return tuple(q[i][-1] for i in range(n))


def stationary(m, cls):
    """Compute one closed irreducible class stationary law, from scratch."""
    c = tuple(cls)
    n = len(c)
    equations = [
        tuple(m[c[i]][c[j]] - (ONE if i == j else ZERO)
              for i in range(n)) for j in range(n-1)
    ]
    eq = equations + [tuple(ONE for _ in c)]
    ans = solve(eq, tuple([ZERO] * (n-1) + [ONE]))
    vec = tuple(ans[c.index(i)] if i in c else ZERO
                for i in range(len(m)))
    assert all(v >= ZERO for v in vec)
    assert sum(vec, ZERO) == ONE
    assert all(sum(vec[i] * m[i][j] for i in range(len(m))) == vec[j]
               for j in range(len(m)))
    return vec


def class_entry_matrix(m, classes):
    """Compute genuine eventual hitting probabilities, not sampled paths.

    For each recurrent class, solve transient first-step harmonic equations
    with its own class boundary 1 and all other recurrent classes 0.
    """
    recurrent = set().union(*(set(c) for c in classes))
    trans = tuple(i for i in range(len(m)) if i not in recurrent)
    result = []
    for cls in classes:
        inside = set(cls)
        coeff = tuple(tuple((ONE if i == j else ZERO) - m[i][j]
                            for j in trans) for i in trans)
        right = tuple(sum((m[i][j] for j in inside), ZERO)
                      for i in trans)
        sol = solve(coeff, right) if trans else ()
        p = tuple(ONE if i in inside else
                  ZERO if i in recurrent else sol[trans.index(i)]
                  for i in range(len(m)))
        assert all(ZERO <= z <= ONE for z in p)
        for i in trans:
            assert p[i] == sum((m[i][j] * p[j] for j in range(len(m))), ZERO)
        result.append(p)
    assert all(sum((p[i] for p in result), ZERO) == ONE
               for i in range(len(m)))
    return tuple(result)


def pushforward(vec, descriptor):
    labels = tuple(sorted(set(descriptor)))
    return tuple(sum((vec[i] for i, d in enumerate(descriptor) if d == x),
                     ZERO) for x in labels)


def finite_sharp(m, classes, basin, descriptor):
    """One copy per distinct *observed* stationary probability law."""
    if not basin or not set(basin).issubset(range(len(m))):
        raise ValueError("invalid or empty predeclared basin")
    weights = class_entry_matrix(m, classes)
    laws = [pushforward(stationary(m, cls), descriptor) for cls in classes]
    return frozenset(law for law, p in zip(laws, weights)
                     if any(p[y] > ZERO for y in basin))


def atom_weights(m, classes, start, descriptor):
    """Aggregate physically different recurrent classes by observed law."""
    if len(start) != len(m) or any(not isinstance(v, F) or v < ZERO
                                  for v in start) or sum(start, ZERO) != ONE:
        raise ValueError("invalid initial law")
    weights = class_entry_matrix(m, classes)
    result = {}
    for cls, p in zip(classes, weights):
        law = pushforward(stationary(m, cls), descriptor)
        mass = sum((start[y] * p[y] for y in range(len(m))), ZERO)
        result[law] = result.get(law, ZERO) + mass
    return {law: mass for law, mass in result.items() if mass != ZERO}


def basis(n, index):
    return tuple(ONE if i == index else ZERO for i in range(n))


def tiny_branch(eps, holding=F(2, 3)):
    if not isinstance(eps, F) or eps < ZERO or eps > ONE:
        raise ValueError("epsilon not in [0,1]")
    if not isinstance(holding, F) or not ZERO <= holding < ONE:
        raise ValueError("invalid holding probability")
    m = (
        (holding, (ONE-holding)*eps, (ONE-holding)*(ONE-eps)),
        (ZERO, ONE, ZERO),
        (ZERO, ZERO, ONE),
    )
    return exact_matrix(m)


class SharpFamilyC5(unittest.TestCase):
    def setUp(self):
        self.m = exact_matrix(M)
        self.id_desc = tuple(range(6))
        self.bool_desc = (0, 0, 1, 1, 1, 1)

    def test_01_independent_row_validation(self):
        self.assertEqual(len(self.m), 6)
        self.assertEqual(self.m[1][1], F(1, 2))
        self.assertEqual(self.m[1][2], F(1, 6))
        self.assertEqual(self.m[1][4], F(1, 3))

    def test_02_unique_stationary_A_B(self):
        self.assertEqual(stationary(self.m, CLASSES[0]),
                         (ZERO, ZERO, F(1, 2), F(1, 2), ZERO, ZERO))
        self.assertEqual(stationary(self.m, CLASSES[1]),
                         (ZERO, ZERO, ZERO, ZERO, F(1, 3), F(2, 3)))

    def test_03_exact_recurrent_selection_not_sampled(self):
        wa, wb = class_entry_matrix(self.m, CLASSES)
        self.assertEqual((wa[0], wb[0]), (F(1, 3), F(2, 3)))
        self.assertEqual((wa[1], wb[1]), (F(1, 3), F(2, 3)))
        self.assertEqual((wa[2], wb[2]), (ONE, ZERO))
        self.assertEqual((wa[3], wb[3]), (ONE, ZERO))
        self.assertEqual((wa[4], wb[4]), (ZERO, ONE))

    def test_04_identity_basin_two_distinct_atoms(self):
        sharp = finite_sharp(self.m, CLASSES, {1, 2}, self.id_desc)
        self.assertEqual(sharp, frozenset([
            stationary(self.m, CLASSES[0]),
            stationary(self.m, CLASSES[1])
        ]))

    def test_05_boolean_descriptor_collapses_physical_classes(self):
        sharp = finite_sharp(self.m, CLASSES, {1, 2}, self.bool_desc)
        self.assertEqual(sharp, frozenset([(ZERO, ONE)]))
        mixed = atom_weights(self.m, CLASSES, basis(6, 1), self.bool_desc)
        self.assertEqual(mixed, {(ZERO, ONE): ONE})

    def test_06_u_start_full_law_not_barycenter(self):
        atoms = atom_weights(self.m, CLASSES, basis(6, 1), self.id_desc)
        self.assertEqual(set(atoms.values()), {F(1, 3), F(2, 3)})
        self.assertEqual(len(atoms), 2)
        barycenter = tuple(F(1, 3) * a + F(2, 3) * b
                           for a, b in zip(stationary(self.m, CLASSES[0]),
                                           stationary(self.m, CLASSES[1])))
        self.assertNotIn(barycenter, atoms)

    def test_07_mixed_initial_law_exact_affine_weights(self):
        mu = tuple(F(1, 5)*a + F(4, 5)*b
                   for a, b in zip(basis(6, 1), basis(6, 2)))
        atoms = atom_weights(self.m, CLASSES, mu, self.id_desc)
        self.assertEqual(atoms[stationary(self.m, CLASSES[0])], F(13, 15))
        self.assertEqual(atoms[stationary(self.m, CLASSES[1])], F(2, 15))
        self.assertEqual(sum(atoms.values(), ZERO), ONE)

    def test_08_nontrivial_A_only_basin(self):
        sharp = finite_sharp(self.m, CLASSES, {2, 3}, self.id_desc)
        self.assertEqual(sharp, frozenset([stationary(self.m, CLASSES[0])]))
        self.assertEqual(len({2, 3}), 2)  # original nontriviality control

    def test_09_coverage_alone_allows_spurious_atoms(self):
        sharp = finite_sharp(self.m, CLASSES, {1, 2}, self.id_desc)
        extra = basis(6, 0)
        declared = sharp | frozenset([extra])
        self.assertTrue(sharp.issubset(declared))  # coverage passes
        self.assertNotEqual(sharp, declared)  # positive-witness gate fails
        self.assertNotIn(extra, atom_weights(self.m, CLASSES,
                                           basis(6, 1), self.id_desc))

    def test_10_omitted_positive_atom_fails_coverage(self):
        sharp = finite_sharp(self.m, CLASSES, {1, 2}, self.id_desc)
        self.assertFalse(sharp.issubset({stationary(self.m, CLASSES[0])}))

    def test_11_arbitrarily_tiny_positive_atom_retained(self):
        for eps in (F(1, 10), F(1, 10**6), F(1, 10**35)):
            m = tiny_branch(eps)
            sharp = finite_sharp(m, ((1,), (2,)), {0}, (0, 1, 2))
            self.assertEqual(len(sharp), 2)
            atoms = atom_weights(m, ((1,), (2,)), basis(3, 0), (0, 1, 2))
            self.assertEqual(atoms[basis(3, 1)], eps)
            self.assertEqual(atoms[basis(3, 2)], ONE-eps)

    def test_12_zero_weight_branch_excluded(self):
        m = tiny_branch(ZERO)
        sharp = finite_sharp(m, ((1,), (2,)), {0}, (0, 1, 2))
        self.assertEqual(sharp, frozenset([basis(3, 2)]))
        atoms = atom_weights(m, ((1,), (2,)), basis(3, 0), (0, 1, 2))
        self.assertEqual(atoms, {basis(3, 2): ONE})

    def test_13_wrong_singleton_target_is_not_exact_gr(self):
        A = stationary(self.m, CLASSES[0])
        B = stationary(self.m, CLASSES[1])
        sharp = finite_sharp(self.m, CLASSES, {1, 2}, self.id_desc)
        self.assertNotEqual(sharp, frozenset([A]))
        self.assertNotEqual(sharp, frozenset([B]))
        self.assertEqual(finite_sharp(self.m, CLASSES, {1, 2}, self.bool_desc),
                         frozenset([(ZERO, ONE)]))

    def test_14_periodic_marginal_not_occupation_limit(self):
        piA = stationary(self.m, CLASSES[0])
        at_even = basis(6, 2)
        at_odd = basis(6, 3)
        self.assertNotEqual(at_even, at_odd)
        self.assertEqual(tuple((at_even[i] + at_odd[i])/2
                               for i in range(6)), piA)

    def test_15_invalid_matrix_and_epsilon_rejected(self):
        for bad in ("0.1", 0.1, F(-1, 20), F(21, 20)):
            with self.assertRaises(ValueError):
                tiny_branch(bad)
        with self.assertRaises(ValueError):
            tiny_branch(F(1, 5), ONE)
        with self.assertRaises(ValueError):
            tiny_branch(F(1, 5), F(-1, 3))
        with self.assertRaises(ValueError):
            exact_matrix(((F(1), F(0)),))
        with self.assertRaises(ValueError):
            exact_matrix(((F(1, 2), F(1, 4)),
                          (F(0), F(1))))
        with self.assertRaises(ValueError):
            exact_matrix(((F(1, 2), 0.5),
                          (F(0), F(1))))


if __name__ == "__main__":
    unittest.main()
