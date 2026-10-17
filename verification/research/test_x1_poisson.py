"""Independent exact checks and destructive controls for X1 Poisson data.

These tests check actual stage-assembled rational rows; Lean must separately
connect its literal certificate to the actual typed kernel and path law.
"""
from fractions import Fraction as F
from itertools import product
import unittest
import x1_commons as C


TARGET = {"E": F(5, 12), "L": F(44984685451641390245, 355006278148174557117)}
L_BIAS = {
    (0, 0, False): F(834232478833826944200, 2248373094938438861741),
    (0, 0, True): F(18536880168967027339580, 6745119284815316585223),
    (0, 1, False): F(323475328327310089470, 2248373094938438861741),
    (0, 1, True): F(15840683281493208845465, 6745119284815316585223),
    (0, 2, False): F(-226150755438709482810, 2248373094938438861741),
    (0, 2, True): F(142848561496669483491113, 67451192848153165852230),
    (1, 1, False): F(0),
    (1, 1, True): F(14444140710994482746480, 6745119284815316585223),
    (1, 2, False): F(-224693274673831558920, 2248373094938438861741),
    (1, 2, True): F(13126041884208197680520, 6745119284815316585223),
    (2, 2, False): F(-304354666295696534880, 2248373094938438861741),
    (2, 2, True): F(11831364758483355705440, 6745119284815316585223),
}


def bias(mode):
    return {y: (F(5, 3) * y[1] if mode == "E" else
                L_BIAS[min(y[0]), max(y[0]), y[1]]) for y in C.STATES}


def residual(K, g, target, y):
    return g[y] - sum((p*g[z] for z, p in K[y].items()), F(0)) - (F(y[1])-target)


class X1PoissonTests(unittest.TestCase):
    def test_every_actual_row_including_both_transient_states(self):
        for mode in ("E", "L"):
            K, g = C.kernel(mode), bias(mode)
            self.assertEqual(len(g), 18)
            self.assertTrue(all(residual(K, g, TARGET[mode], y) == 0 for y in C.STATES))
        excluded = set(C.STATES) - C.reachable(C.kernel("L"))
        self.assertEqual(excluded, {((0, 2), True), ((2, 0), True)})

    def test_wrong_occupation_target_is_rejected_by_every_row(self):
        K, g = C.kernel("L"), bias("L")
        wrong = TARGET["L"] + F(1, 100)
        self.assertTrue(all(residual(K, g, wrong, y) == F(1, 100) for y in C.STATES))

    def test_transient_bias_tampering_is_not_hidden_by_stationary_checks(self):
        K, g = C.kernel("L"), bias("L")
        transient = ((0, 2), True)
        pi = C.stationary(K, C.reachable(K))
        self.assertEqual(pi.get(transient, F(0)), 0)
        g[transient] += F(1)
        self.assertNotEqual(residual(K, g, TARGET["L"], transient), 0)
        # An invariant-weighted aggregate alone would miss this corruption.
        self.assertEqual(sum((p*residual(K, g, TARGET["L"], y)
                              for y, p in pi.items()), F(0)), 0)

    def test_equilibrium_physical_law_is_not_globally_unique(self):
        K, laws = C.kernel("E"), []
        for memory in product(range(3), repeat=2):
            pi = {(memory, False): F(7, 12), (memory, True): F(5, 12)}
            for z in C.STATES:
                self.assertEqual(sum((p*K[y].get(z, F(0)) for y, p in pi.items()), F(0)),
                                 pi.get(z, F(0)))
            self.assertEqual(sum(p for y, p in pi.items() if y[1]), TARGET["E"])
            laws.append(pi)
        self.assertEqual(len(laws), 9)
        self.assertNotEqual(laws[0], laws[-1])


if __name__ == "__main__":
    unittest.main()
