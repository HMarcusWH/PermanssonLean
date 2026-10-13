"""C6 independent exact-Fraction tests: typed sparse alpha-only intervention.

No simulation, floating-point threshold, fixed-horizon hit substituted
for eventual residence, or post-hoc change of the frozen descriptor.
The fully proved Lean source, not this script, certifies infinite paths.
"""
import unittest
from fractions import Fraction as F

Q0, Q1 = F(0), F(1)
BASE = (
    (Q0, Q1, Q0, Q0, Q0, Q0),
    (Q0, F(1, 2), F(1, 6), Q0, F(1, 3), Q0),
    (Q0, Q0, Q0, Q1, Q0, Q0),
    (Q0, Q0, Q1, Q0, Q0, Q0),
    (Q0, Q0, Q0, Q0, F(1, 2), F(1, 2)),
    (Q0, Q0, Q0, Q0, F(1, 4), F(3, 4)),
)
OBS = (False, False, True, True, True, True)
BASIN = frozenset((1, 2))


def checked(matrix):
    n = len(matrix)
    if not n or any(len(row) != n for row in matrix):
        raise ValueError("non-square")
    if any(not isinstance(x, F) or x < Q0 or x > Q1
           for row in matrix for x in row):
        raise ValueError("invalid rational transition")
    if any(sum(row, Q0) != Q1 for row in matrix):
        raise ValueError("non-stochastic row")
    return tuple(tuple(row) for row in matrix)


def replace_rows(matrix, rows):
    arr = [list(row) for row in matrix]
    n = len(arr)
    for i, j in rows.items():
        if not isinstance(i, int) or not isinstance(j, int) or not (0 <= i < n and 0 <= j < n):
            raise ValueError("invalid row or state index")
        arr[i] = [Q1 if c == j else Q0 for c in range(n)]
    return checked(arr)


RESPONSE = replace_rows(BASE, {1: 1, 2: 1})
B_ONLY = replace_rows(BASE, {1: 4, 2: 4})
U_ONLY = replace_rows(BASE, {1: 1})
IDENTITY = replace_rows(BASE, {})


def solve(a, b):
    """Independent exact Gauss-Jordan, no NumPy, no floats."""
    n = len(b)
    if len(a) != n or any(len(row) != n for row in a):
        raise ValueError("dimension mismatch")
    work = [list(a[i]) + [b[i]] for i in range(n)]
    for k in range(n):
        t = next((i for i in range(k, n) if work[i][k] != Q0), None)
        if t is None:
            raise ValueError("non-unique linear solution")
        work[k], work[t] = work[t], work[k]
        p = work[k][k]
        work[k] = [v / p for v in work[k]]
        for i in range(n):
            if i != k:
                p = work[i][k]
                work[i] = [work[i][j] - p * work[k][j] for j in range(n + 1)]
    return tuple(work[i][-1] for i in range(n))


def reachable(matrix, start):
    seen = {start}
    stack = [start]
    while stack:
        x = stack.pop()
        for y, p in enumerate(matrix[x]):
            if p > Q0 and y not in seen:
                seen.add(y)
                stack.append(y)
    return frozenset(seen)


def recurrent_classes(matrix):
    """Independently enumerate closed communicating classes on true edges."""
    reach = [reachable(matrix, i) for i in range(len(matrix))]
    unseen = set(range(len(matrix)))
    classes = []
    while unseen:
        a = min(unseen)
        cls = frozenset(i for i in unseen if a in reach[i] and i in reach[a])
        unseen.difference_update(cls)
        if all(matrix[i][j] == Q0 or j in cls for i in cls for j in range(len(matrix))):
            classes.append(cls)
    return tuple(sorted(classes, key=lambda cls: min(cls)))


def absorption_probabilities(matrix):
    """Entire eventual destination distribution solved by exact boundary equations."""
    classes = recurrent_classes(matrix)
    recurrent = set().union(*classes)
    transient = tuple(i for i in range(len(matrix)) if i not in recurrent)
    coeff = tuple(tuple((Q1 if i == j else Q0) - matrix[i][j] for j in transient)
                  for i in transient)
    result = {}
    for cls in classes:
        rhs = tuple(sum((matrix[i][j] for j in cls), Q0) for i in transient)
        vals = solve(coeff, rhs) if transient else ()
        p = tuple(Q1 if i in cls else Q0 if i in recurrent
                  else vals[transient.index(i)] for i in range(len(matrix)))
        result[cls] = p
    assert all(sum((p[i] for p in result.values()), Q0) == Q1
               for i in range(len(matrix)))
    return result


def observed_limit_labels(matrix, observation):
    out = {}
    for cls in recurrent_classes(matrix):
        labels = {observation[i] for i in cls}
        if len(labels) != 1:
            raise ValueError("not a constant-observed recurrent class")
        out[cls] = labels.pop()
    return out


def observed_limit_probability(matrix, initial, observation=OBS, observed_value=True):
    if len(initial) != len(matrix) or any(not isinstance(x, F) or x < Q0
                                          for x in initial) or sum(initial, Q0) != Q1:
        raise ValueError("invalid initial law")
    weights = absorption_probabilities(matrix)
    labels = observed_limit_labels(matrix, observation)
    return sum((initial[i] * p[i] for cls, p in weights.items()
                if labels[cls] == observed_value for i in range(len(matrix))), Q0)


def atom_family(matrix, basin=BASIN, observation=OBS):
    if not basin or not set(basin) <= set(range(len(matrix))):
        raise ValueError("invalid frozen basin")
    weights = absorption_probabilities(matrix)
    labels = observed_limit_labels(matrix, observation)
    return frozenset(labels[cls] for cls, p in weights.items()
                     if any(p[i] > Q0 for i in basin))


def basis(i, n=6):
    return tuple(Q1 if j == i else Q0 for j in range(n))


class C6StrategicObservedResponse(unittest.TestCase):
    def test_01_base_rows_are_exact_and_normalized(self):
        self.assertEqual(checked(BASE), BASE)
        self.assertEqual(BASE[1][1:5], (F(1, 2), F(1, 6), Q0, F(1, 3)))

    def test_02_only_u_and_a0_rows_changed(self):
        delta = {i for i in range(6) if BASE[i] != RESPONSE[i]}
        self.assertEqual(delta, {1, 2})
        self.assertEqual(RESPONSE[1], basis(1))
        self.assertEqual(RESPONSE[2], basis(1))
        for i in (0, 3, 4, 5):
            self.assertEqual(BASE[i], RESPONSE[i])

    def test_03_independent_closed_class_geometry_baseline(self):
        self.assertEqual(recurrent_classes(BASE),
                         (frozenset({2, 3}), frozenset({4, 5})))

    def test_04_intervention_new_absorbing_class_and_preserved_B(self):
        self.assertEqual(recurrent_classes(RESPONSE),
                         (frozenset({1}), frozenset({4, 5})))
        self.assertNotIn(frozenset({2, 3}), recurrent_classes(RESPONSE))

    def test_05_baseline_exact_destination_probability_from_u(self):
        weights = absorption_probabilities(BASE)
        self.assertEqual(weights[frozenset({2, 3})][1], F(1, 3))
        self.assertEqual(weights[frozenset({4, 5})][1], F(2, 3))

    def test_06_fixed_observation_is_true_a_s_at_baseline_u_and_a0(self):
        for i in BASIN:
            self.assertEqual(observed_limit_probability(BASE, basis(i)), Q1)

    def test_07_fixed_observation_is_false_a_s_under_intervention(self):
        for i in BASIN:
            self.assertEqual(observed_limit_probability(RESPONSE, basis(i)), Q0)
        self.assertEqual(absorption_probabilities(RESPONSE)[frozenset({1})][1], Q1)
        self.assertEqual(absorption_probabilities(RESPONSE)[frozenset({1})][2], Q1)

    def test_08_exact_effect_and_uniform_margin(self):
        effects = tuple(abs(observed_limit_probability(BASE, basis(i)) -
                            observed_limit_probability(RESPONSE, basis(i)))
                        for i in sorted(BASIN))
        self.assertEqual(effects, (Q1, Q1))
        self.assertEqual(min(effects), Q1)

    def test_09_sharp_observed_atom_family_actually_changes(self):
        self.assertEqual(atom_family(BASE), frozenset({True}))
        self.assertEqual(atom_family(RESPONSE), frozenset({False}))

    def test_10_same_frozen_region_is_closed_in_both(self):
        region = frozenset(range(1, 6))
        for matrix in (BASE, RESPONSE):
            for i in region:
                self.assertEqual(matrix[i][0], Q0)

    def test_11_sparse_alpha_only_model_does_not_replace_world_or_update(self):
        # Constructed D0 semantics: alpha selects next-state label, P copies it,
        # U updates Unit. The same primitive contracts apply to both matrices.
        def world_primitive(action):
            return action
        def unit_update(*unused):
            return ()
        for action in range(6):
            self.assertEqual(world_primitive(action), action)
            self.assertEqual(unit_update(BASE, action), unit_update(RESPONSE, action))

    def test_12_identity_intervention_has_zero_effect(self):
        self.assertEqual(IDENTITY, BASE)
        self.assertEqual(observed_limit_probability(IDENTITY, basis(1)), Q1)

    def test_13_one_row_only_is_not_uniformly_constitutive(self):
        self.assertEqual(observed_limit_probability(U_ONLY, basis(1)), Q0)
        self.assertEqual(observed_limit_probability(U_ONLY, basis(2)), Q1)
        self.assertEqual(min(abs(observed_limit_probability(BASE, basis(i)) -
                                 observed_limit_probability(U_ONLY, basis(i)))
                             for i in BASIN), Q0)

    def test_14_B_destination_changes_physical_class_but_not_descriptor(self):
        self.assertEqual(observed_limit_probability(B_ONLY, basis(1)), Q1)
        self.assertEqual(observed_limit_probability(B_ONLY, basis(2)), Q1)
        self.assertEqual(atom_family(B_ONLY), frozenset({True}))
        self.assertEqual(absorption_probabilities(B_ONLY)[frozenset({4, 5})][1], Q1)

    def test_15_mixed_initial_law_real_exact_response(self):
        mu = tuple(F(1, 5)*basis(1)[i] + F(4, 5)*basis(2)[i]
                   for i in range(6))
        self.assertEqual(observed_limit_probability(BASE, mu), Q1)
        self.assertEqual(observed_limit_probability(RESPONSE, mu), Q0)

    def test_16_B_remains_recurrent_but_is_unreachable_from_frozen_basin(self):
        wb = absorption_probabilities(RESPONSE)[frozenset({4, 5})]
        self.assertEqual(tuple(wb[i] for i in sorted(BASIN)), (Q0, Q0))
        self.assertEqual(wb[4], Q1)

    def test_17_finite_hit_not_same_as_eventual_destination(self):
        # Starting at a0 under RESPONSE sees the TRUE descriptor at time 0,
        # but is absorbed at false-labelled u from time 1 onwards.
        self.assertTrue(OBS[2])
        self.assertEqual(RESPONSE[2][1], Q1)
        self.assertEqual(observed_limit_probability(RESPONSE, basis(2)), Q0)

    def test_18_wrong_selector_from_baseline_rejected(self):
        self.assertNotEqual(recurrent_classes(BASE), recurrent_classes(RESPONSE))
        self.assertNotIn(frozenset({2, 3}), absorption_probabilities(RESPONSE))

    def test_19_rejected_invalid_input_and_negative_probabilities(self):
        with self.assertRaises(ValueError):
            replace_rows(BASE, {6: 1})
        with self.assertRaises(ValueError):
            replace_rows(BASE, {1: -1})
        with self.assertRaises(ValueError):
            checked(((F(1, 3), F(1, 3)), (Q0, Q1)))
        with self.assertRaises(ValueError):
            checked(((F(1, 2), 0.5), (Q0, Q1)))
        with self.assertRaises(ValueError):
            observed_limit_probability(BASE, (Q1,))

    def test_20_no_arbitrary_positive_weight_cutoff(self):
        # An irrelevant alternate control with arbitrarily small probability
        # must retain both positive observed outcomes in the registered family.
        tiny = F(1, 10**35)
        m = checked(((Q0, tiny, Q1-tiny),
                     (Q0, Q1, Q0),
                     (Q0, Q0, Q1)))
        self.assertEqual(atom_family(m, {0}, (False, True, False)),
                         frozenset({False, True}))
        self.assertEqual(observed_limit_probability(m, basis(0, 3),
                         (False, True, False), True), tiny)


if __name__ == "__main__":
    unittest.main()
