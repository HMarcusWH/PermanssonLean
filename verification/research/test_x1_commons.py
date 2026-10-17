"""Independent exact tests for the frozen X1 candidate, without PR/EGR promotion."""
from fractions import Fraction as F
from itertools import product
import unittest

import x1_commons as C


def enumerate_paths(mode, horizon, restrain=False, reset=False, start=C.START):
    """Direct stage enumeration, independent of the assembled matrix iterator."""
    paths = {(start,): F(1)}
    for _ in range(horizon):
        nxt = {}
        for w, p in paths.items():
            y = w[-1]
            for a in C.ACTIONS:
                rate = C.extraction(mode, y)
                pa = F(a == (False, False)) if restrain else (
                    (rate[0] if a[0] else 1-rate[0]) * (rate[1] if a[1] else 1-rate[1]))
                for x in C.BOOL:
                    px = C.p_rep(y[1], a) if x else 1-C.p_rep(y[1], a)
                    z = (C.update(mode, y, a, reset), x)
                    if pa*px:
                        nxt[w+(z,)] = nxt.get(w+(z,), F(0)) + p*pa*px
        paths = nxt
    return paths


class X1IncentiveTests(unittest.TestCase):
    def test_both_players_bellman_and_all_pure_deviations(self):
        """Mirrors bellman_equation, no_pure_deviation, support_equality."""
        for i, x in product(range(2), C.BOOL):
            p = F(1, 2) if x else F(0)
            qs = [C.deviation(i, x, a) for a in C.BOOL]
            self.assertEqual((1-p)*qs[0] + p*qs[1], C.value(i, x))
            for a, q in zip(C.BOOL, qs):
                self.assertLessEqual(q, C.value(i, x))
                if p if a else 1-p:
                    self.assertEqual(q, C.value(i, x))
            if not x:
                self.assertEqual(qs[1]-qs[0], F(-9, 211))

    def test_mixed_deviations_and_non_equilibrium_falsifiers(self):
        for i, x, p in product(range(2), C.BOOL, [F(k, 13) for k in range(14)]):
            self.assertLessEqual((1-p)*C.deviation(i, x, False)+p*C.deviation(i, x, True), C.value(i, x))
        # Dropping congestion destroys the registered equilibrium conditions.
        for i in range(2):
            self.assertGreater(C.deviation(i, True, True, chi=F(0)), C.value(i, True))
        # Optimizing under a different physical P also fails the certificate.
        wrong = lambda y, a: {True: F(1), False: F(0)}
        self.assertTrue(any(C.deviation(i, x, a, physical_world=wrong) > C.value(i, x)
                            for i, x, a in product(range(2), C.BOOL, C.BOOL)))
        self.assertEqual(C.reward(0, True, (True, False)), F(1, 2))
        self.assertEqual(C.reward(1, True, (True, False)), 0)


class X1TypedModelTests(unittest.TestCase):
    def test_full_probability_rows_same_world_and_memory_nonvacuity(self):
        self.assertEqual(len(C.STATES), 18)
        for mode in ("E", "L"):
            K = C.kernel(mode)
            for y in C.STATES:
                self.assertEqual(sum(K[y].values()), 1)
                for a in C.ACTIONS:
                    self.assertEqual(C.world(y, a), C.world(((2, 0), y[1]), a))
        low, high = ((0, 0), True), ((2, 2), True)
        self.assertNotEqual(C.action_law("L", low), C.action_law("L", high))
        self.assertEqual(C.action_law("E", low), C.action_law("E", high))
        self.assertNotEqual(C.update("L", C.START, (False, False)), C.START[0])
        self.assertEqual(C.update("E", C.START, (True, True)), C.START[0])

    def test_reinforcement_against_independent_integer_rule(self):
        for y, a in product(C.STATES, C.ACTIONS):
            ref = F(1 if y[1] else -1, 20)
            expected = []
            for i in range(2):
                payoff = (F(1, 2) if y[1] else 0)*a[i] - F(193, 211)*a[i]*a[1-i] - F(1, 10)*(not y[1])
                sign = 1 if payoff > ref else -1 if payoff < ref else 0
                step = sign if a[i] else -sign
                expected.append(max(0, min(2, y[0][i]+step)))
            self.assertEqual(C.update("L", y, a), tuple(expected))

    def test_stage_order_and_hidden_memory_falsifiers(self):
        e, l = C.kernel("E"), C.kernel("L")
        self.assertNotEqual(e[C.START], l[C.START])
        self.assertEqual(sum(p for y, p in e[C.START].items() if y[1]), F(13, 20))
        self.assertEqual(sum(p for y, p in l[C.START].items() if y[1]), F(13, 20))
        for start in C.COMPARISON_STARTS:
            self.assertEqual(C.replete_at(l, 1, start), C.replete_at(C.kernel("L", reset=True), 1, start))
        # Action and joint interventions agree for the selected world property,
        # while they have distinct full memory laws. No universal null-U claim.
        self.assertNotEqual(C.kernel("L", restrain=True)[C.START],
                            C.kernel("L", restrain=True, reset=True)[C.START])
        self.assertEqual(C.replete_at(C.kernel("L", restrain=True)),
                         C.replete_at(C.kernel("L", restrain=True, reset=True)))
        self.assertEqual(C.update("L", ((1, 1), True), (True, False)), (2, 2))
        self.assertEqual(C.update("L", ((1, 1), False), (True, False)), (0, 2))

    def test_paths_match_matrix_properties_and_killed_recursion(self):
        for mode, horizon in product(("E", "L"), range(4)):
            K = C.kernel(mode)
            paths = enumerate_paths(mode, horizon)
            self.assertEqual(sum(paths.values()), 1)
            survival = sum((p for w, p in paths.items() if all(y in C.REGION for y in w)), F(0))
            terminal = sum((p for w, p in paths.items() if w[-1] in C.REGION), F(0))
            self.assertEqual(survival, C.killed_persistence(K, horizon))
            self.assertEqual(terminal, C.replete_at(K, horizon))
            if horizon >= 2:
                self.assertGreater(terminal, survival)  # exit-and-re-entry is allowed only by ψ

    def test_leaking_region_not_exact_gr_and_persistence_decay(self):
        for mode in ("E", "L"):
            K = C.kernel(mode)
            self.assertEqual(C.killed_persistence(K, 1), F(13, 20))
            self.assertLess(C.killed_persistence(K, 1), 1)
            for horizon in (2, 3, 5, 20):
                self.assertLessEqual(C.killed_persistence(K, horizon), F(9, 10)**horizon)
            for y in C.REGION:
                self.assertLessEqual(sum(p for z, p in K[y].items() if z in C.REGION), F(9, 10))

    def test_stationary_laws_verified_exactly_and_distinct(self):
        occupations = []
        for mode, count in (("E", 2), ("L", 16)):
            K = C.kernel(mode)
            states = C.reachable(K)
            self.assertEqual(len(states), count)
            pi = C.stationary(K, states)
            self.assertEqual(sum(pi.values()), 1)
            self.assertTrue(all(p > 0 for p in pi.values()))
            for z in C.STATES:
                self.assertEqual(sum(p*K[y].get(z, 0) for y, p in pi.items()), pi.get(z, 0))
            occupations.append(sum(p for y, p in pi.items() if y[1]))
        self.assertEqual(occupations[0], F(5, 12))
        self.assertEqual(occupations[1], F(44984685451641390245, 355006278148174557117))
        self.assertNotEqual(*occupations)  # must not hide distinct targets behind one ν

    def test_independently_reconstructed_exact_reference_values(self):
        """Fractions independently reconstructed by a separate mathematical audit."""
        expected = {
            "E": {"baseline": F(227, 500), "action": F(3171, 4000),
                  "update": F(227, 500), "joint": F(3171, 4000)},
            "L": {"baseline": F(8381459, 32000000), "action": F(3171, 4000),
                  "update": F(41417, 128000), "joint": F(3171, 4000)}}
        for mode, values in expected.items():
            for name, flags in {"baseline": (False, False), "action": (True, False),
                                "update": (False, True), "joint": (True, True)}.items():
                self.assertEqual(C.replete_at(C.kernel(mode, *flags)), values[name])
        self.assertEqual(C.killed_persistence(C.kernel("E"), 2), F(169, 400))
        self.assertEqual(C.killed_persistence(C.kernel("L"), 2), F(257, 800))

    def test_interventions_full_path_values_and_categorical_receipt(self):
        for mode, restrain, reset in product(("E", "L"), C.BOOL, C.BOOL):
            paths = enumerate_paths(mode, C.PROPERTY_HORIZON, restrain, reset)
            expected = sum((p for w, p in paths.items() if w[-1] in C.REGION), F(0))
            self.assertEqual(expected, C.replete_at(C.kernel(mode, restrain, reset)))
        data = C.receipt()
        self.assertEqual(len(data["application_categories"]), 9)
        self.assertTrue(all(isinstance(v, str) for v in data["application_categories"].values()))
        # E ignores memory, L is sensitive to reset; exact declared property, not a plot.
        self.assertEqual(data["modes"]["E"]["singleton_effects"]["update"], "0")
        self.assertNotEqual(data["modes"]["L"]["singleton_effects"]["update"], "0")
        # Original pathLawNontrivial needs TWO distinct starts; stochasticity
        # inside the one registered path law cannot repair this gate.
        self.assertEqual(len(C.POINTWISE_STARTS), 1)
        self.assertEqual(C.BASIN, C.REGION)
        self.assertEqual(C.COMPARISON_STARTS, C.REGION)
        self.assertEqual(len(C.COMPARISON_STARTS), 9)
        self.assertNotIn("constitutive_margins", data["modes"]["E"])

    def test_prospective_full_region_infima_check_every_start(self):
        """Design v2: all nine original replete starts, with no outcome-selected
        subset. Direct finite path enumeration independently checks every effect."""
        data = C.receipt()
        for mode in ("E", "L"):
            baseline = {y: C.replete_at(C.kernel(mode), start=y) for y in C.COMPARISON_STARTS}
            for name, flags in {"action": (True, False), "update": (False, True),
                                "joint": (True, True)}.items():
                effects = []
                for y in C.COMPARISON_STARTS:
                    paths = enumerate_paths(mode, C.PROPERTY_HORIZON, *flags, start=y)
                    changed = sum((p for w, p in paths.items() if w[-1] in C.REGION), F(0))
                    effects.append(abs(changed-baseline[y]))
                self.assertEqual(str(min(effects)), data["modes"][mode]["finite_matrix_effect_infima"][name])
                self.assertEqual(len(data["modes"][mode]["finite_matrix_effects_by_start"][name]), 9)
        # Independently reconstructed infima, registered only after prospective v2.
        self.assertEqual(data["modes"]["E"]["finite_matrix_effect_infima"],
                         {"action": "271/800", "update": "0", "joint": "271/800"})
        self.assertEqual(data["modes"]["L"]["finite_matrix_effect_infima"],
                         {"action": "3010663529/6400000000", "update": "1244820951/25600000000",
                          "joint": "3010663529/6400000000"})
        self.assertEqual(data["modes"]["E"]["finite_matrix_direction"]["update"], "zero at all nine starts")
        self.assertTrue(all(v == "strict increase at all nine starts"
                            for v in data["modes"]["L"]["finite_matrix_direction"].values()))


if __name__ == "__main__":
    unittest.main()
