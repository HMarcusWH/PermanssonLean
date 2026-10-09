"""D0-F canonical record, independently checked math, and adversarial integrity tests."""
from dataclasses import replace
from fractions import Fraction as Q
import json
import unittest

from d0_finite_solver import value_by_recursion, value_by_enumeration
from d0_certificate import (
    CertificateError, CertificateResourceLimit, MAX_BYTES,
    canonical_bytes, make_certificate, normalize_problem, parse_json_strict,
    problem_digest,
)
from d0_recheck_certificate import (
    GOOD, BAD, LIMIT, check_certificate, forward_first_hit_value,
)

HALF = ((Q(1, 2), Q(1, 2)), (Q(0), Q(1)))
SURE = ((Q(0), Q(1)), (Q(0), Q(1)))
STAY = ((Q(1), Q(0)), (Q(0), Q(1)))
G, D = [1], []
# Existing D0 Python 3-state fixture: (0 initial, 1 goal, 2 forbidden).
A = ((Q(1, 2), Q(1, 2), Q(0)),
     (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(1)))
B = ((Q(0), Q(3, 4), Q(1, 4)),
     (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(1)))
C = ((Q(1, 4), Q(1, 4), Q(1, 2)),
     (Q(0), Q(1), Q(0)), (Q(0), Q(0), Q(1)))


def fixture_two():
    return make_certificate([("half", HALF), ("sure", SURE)],
                            HALF, 0, G, D, 1)


def fixture_three():
    return make_certificate([("A", A), ("B", B), ("C", C)],
                            A, 0, [1], [2], 1)


class D0CertificateTests(unittest.TestCase):
    def test_lean_two_state_witness_values_and_winner(self):
        c = fixture_two()
        r = parse_json_strict(c)
        self.assertEqual([x["value"] for x in r["calculation"]["values"]],
                         [[1, 2], [1, 1]])
        self.assertEqual(r["calculation"]["selected"], "sure")
        self.assertEqual(r["calculation"]["value"], [1, 1])
        self.assertEqual(check_certificate(c).status, GOOD)

    def test_three_state_winner_and_horizon(self):
        r = parse_json_strict(fixture_three())
        self.assertEqual([x["value"] for x in r["calculation"]["values"]],
                         [[1, 2], [3, 4], [1, 4]])
        self.assertEqual(r["calculation"]["selected"], "B")
        self.assertEqual(check_certificate(fixture_three()).status, GOOD)
        higher = make_certificate([("A", A), ("B", B)], A, 0, [1], [2], 3)
        self.assertEqual(parse_json_strict(higher)["calculation"]["selected"], "A")
        self.assertEqual(check_certificate(higher).status, GOOD)

    def test_byte_identical_regeneration(self):
        one = fixture_three()
        two = make_certificate([("A", A), ("B", B), ("C", C)],
                               A, 0, (i for i in [1]), (i for i in [2]), 1)
        self.assertEqual(one, two)
        self.assertTrue(one.endswith(b"\n"))
        self.assertEqual(one, canonical_bytes(parse_json_strict(one)))

    def test_external_expected_input_prevents_valid_replacement(self):
        original = parse_json_strict(fixture_two())
        original_digest = original["problem_sha256"]
        altered = make_certificate([("stay", STAY), ("sure", SURE)],
                                   HALF, 0, G, D, 1)
        # Both reports are internally consistent. Only the separately
        # supplied expected problem digest binds identity of the input.
        self.assertEqual(check_certificate(altered).status, GOOD)
        self.assertEqual(check_certificate(fixture_two(), original_digest).status, GOOD)
        self.assertEqual(check_certificate(altered, original_digest).status, BAD)
        self.assertEqual(check_certificate(altered, "not-a-digest").status, BAD)

    def test_tampered_calculation_values_and_winner(self):
        baseline = parse_json_strict(fixture_three())
        for field, value in [("selected", "A"), ("value", [1, 1])]:
            mutated = json.loads(json.dumps(baseline))
            mutated["calculation"][field] = value
            self.assertEqual(check_certificate(canonical_bytes(mutated)).status, BAD)
        for operation in ("value", "drop", "order", "label"):
            mutated = json.loads(json.dumps(baseline))
            if operation == "value":
                mutated["calculation"]["values"][0]["value"] = [1, 3]
            elif operation == "drop":
                mutated["calculation"]["values"].pop()
            elif operation == "order":
                mutated["calculation"]["values"].reverse()
            else:
                mutated["calculation"]["values"][1]["label"] = "unlisted"
            self.assertEqual(check_certificate(canonical_bytes(mutated)).status, BAD)

    def test_changed_query_without_digest_recomputation(self):
        raw = parse_json_strict(fixture_two())
        for key, changed in [("initial", 1), ("goal", []),
                             ("forbidden", [0]), ("horizon", 2)]:
            mutated = json.loads(json.dumps(raw))
            mutated["problem"][key] = changed
            self.assertEqual(check_certificate(canonical_bytes(mutated)).status, BAD)

    def test_matrix_change_without_digest_recomputation(self):
        mutated = parse_json_strict(fixture_two())
        mutated["problem"]["menu"][1]["rows"] = [[1, 1], [0, 1]]
        self.assertEqual(check_certificate(canonical_bytes(mutated)).status, BAD)

    def test_ties_are_first_listed(self):
        raw = make_certificate([("first", SURE), ("second", SURE)],
                               HALF, 0, G, D, 2)
        self.assertEqual(parse_json_strict(raw)["calculation"]["selected"], "first")
        self.assertEqual(check_certificate(raw).status, GOOD)
        changed = parse_json_strict(raw)
        changed["calculation"]["selected"] = "second"
        self.assertEqual(check_certificate(canonical_bytes(changed)).status, BAD)

    def test_baseline_is_not_implicitly_selected(self):
        raw = make_certificate([("only_stay", STAY)], SURE, 0, G, D, 2)
        rec = parse_json_strict(raw)
        self.assertEqual(rec["calculation"]["selected"], "only_stay")
        self.assertEqual(rec["calculation"]["value"], [0, 1])
        self.assertEqual(check_certificate(raw).status, GOOD)

    def test_initial_membership_and_forbidden_before_late_goal(self):
        for start, goal, danger, expected in [
            (1, [1], [2], Q(1)), (2, [1], [2], Q(0)),
            (0, [1], [2], Q(0)), (0, [], [], Q(0)),
            (0, [0], [], Q(1))
        ]:
            matrix = A
            t = 0
            raw = make_certificate([("m", matrix)], matrix,
                                   start, goal, danger, t)
            self.assertEqual(check_certificate(raw).status, GOOD)
            self.assertEqual(
                parse_json_strict(raw)["calculation"]["value"],
                [expected.numerator, expected.denominator])
        dangerous = ((Q(0), Q(0), Q(1)),
                     (Q(0), Q(1), Q(0)), (Q(0), Q(1), Q(0)))
        raw = make_certificate([("danger_then_goal", dangerous)],
                               dangerous, 0, [1], [2], 2)
        self.assertEqual(parse_json_strict(raw)["calculation"]["value"], [0, 1])
        self.assertEqual(check_certificate(raw).status, GOOD)

    def test_three_independent_exact_engines_small_cases(self):
        for matrix in (A, B, C):
            for t in range(5):
                for start in range(3):
                    expected = value_by_recursion(matrix, start, [1], [2], t)
                    self.assertEqual(forward_first_hit_value(matrix, start, [1], [2], t),
                                     expected)
                    self.assertEqual(value_by_enumeration(matrix, start, [1], [2], t),
                                     expected)

    def test_strict_json_and_schema(self):
        good = fixture_two()
        for malformed in (
            good[:-1], good + b" ", b'{"x":1,"x":2}\n',
            b'{"x":NaN}\n', b'{"x":0.5}\n', b'{"x":true}\n',
        ):
            self.assertEqual(check_certificate(malformed).status, BAD)
        for field, value in [("scope", "PROVED_OPTIMUM"),
                             ("schema", "unknown")]:
            mutated = parse_json_strict(good)
            mutated[field] = value
            self.assertEqual(check_certificate(canonical_bytes(mutated)).status, BAD)
        mutated = parse_json_strict(good)
        mutated["extra"] = 42
        self.assertEqual(check_certificate(canonical_bytes(mutated)).status, BAD)
        mutated = parse_json_strict(good)
        mutated["problem"]["goal"] = [1, 1]
        mutated["problem_sha256"] = problem_digest(mutated["problem"])
        self.assertEqual(check_certificate(canonical_bytes(mutated)).status, BAD)

    def test_rational_pair_canonicality_and_bool_rejection(self):
        good = parse_json_strict(fixture_two())
        for pair in ([2, 4], [0, 2], [1, 0], [-1, -2],
                     [True, 1], [0.5, 1], ["1", 2], [0, False]):
            mutated = json.loads(json.dumps(good))
            mutated["calculation"]["values"][0]["value"] = pair
            self.assertEqual(check_certificate(canonical_bytes(mutated)).status, BAD)
        with self.assertRaises(CertificateError):
            make_certificate([("half", ((0.5, 0.5), (0, 1)))], HALF, 0, G, D, 1)
        with self.assertRaises(CertificateError):
            make_certificate([("half", HALF)], HALF, False, G, D, 1)

    def test_candidate_and_target_input_rejection(self):
        with self.assertRaises(CertificateError):
            make_certificate([], HALF, 0, G, D, 1)
        with self.assertRaises(CertificateError):
            make_certificate([("A", HALF), ("A", SURE)], HALF, 0, G, D, 1)
        with self.assertRaises(CertificateError):
            make_certificate([("A", HALF)], HALF, 0, [1], [1], 1)
        with self.assertRaises(CertificateError):
            make_certificate([("A", HALF)], HALF, 0, [True], [], 1)
        with self.assertRaises(CertificateError):
            make_certificate([("A", A)], HALF, 0, G, D, 1)
        with self.assertRaises(CertificateError):
            make_certificate([("A", HALF)], HALF, 0, G, D, True)

    def test_unreachable_goal_still_bounds_active_mass_growth(self):
        """Codex P1 regression: won stays zero while active denominators grow."""
        denom = 1 << 252
        dense = ((Q(denom - 1, denom), Q(1, denom)),
                 (Q(1, denom), Q(denom - 1, denom)))
        raw = make_certificate([("unreachable", dense)], dense, 0, [], [], 60)
        record = parse_json_strict(raw)
        self.assertEqual(record["calculation"]["value"], [0, 1])
        self.assertEqual(check_certificate(raw).status, LIMIT)

    def test_backward_generation_bounds_intermediate_rationals(self):
        """Codex P2 regression: generator stops before 252-bit row powers explode."""
        denominator = 1 << 252
        slow = ((Q(denominator - 1, denominator), Q(1, denominator)),
                (Q(0), Q(1)))
        with self.assertRaises(CertificateResourceLimit):
            make_certificate([("slow_goal", slow)], slow, 0, [1], [], 60)
        # Without a resource limit the same mathematical recursion is defined.
        self.assertEqual(value_by_recursion(slow, 1, [1], [], 0), Q(1))

    def test_oversized_declared_problem_bounds_are_resource_limits(self):
        """Codex P2 regression: distinguish bounds from malformed inputs."""
        source = parse_json_strict(fixture_two())
        for name, value in (("dimension", 13), ("horizon", 129)):
            changed = json.loads(json.dumps(source))
            changed["problem"][name] = value
            self.assertEqual(check_certificate(canonical_bytes(changed)).status, LIMIT)
        for name, value in (("dimension", 0), ("horizon", -1)):
            changed = json.loads(json.dumps(source))
            changed["problem"][name] = value
            self.assertEqual(check_certificate(canonical_bytes(changed)).status, BAD)

    def test_resource_limit_is_distinct_from_invalid(self):
        self.assertEqual(check_certificate(b" " * (MAX_BYTES + 1)).status, LIMIT)
        with self.assertRaises(CertificateResourceLimit):
            make_certificate([("A", HALF)], HALF, 0, G, D, 129)
        with self.assertRaises(CertificateResourceLimit):
            make_certificate([("A", HALF)], HALF, 0, G, D, 1000000)


if __name__ == "__main__":
    unittest.main()
