"""C10 v1.1 state-relabeling and menu-permutation metamorphic checks.

Unlike the generated identity-only enumerations, these transformations
preserve the *entire* numerical problem's semantics while changing
physical state names or declared intervention index order.
Both the source and transformed receipts are independently rechecked.
"""
from __future__ import annotations

from copy import deepcopy
from fractions import Fraction as Q
import unittest

from c10_exact_execution import check_input, execute
from c10_golden import six_input
from c10_verify_receipt import verify_receipt


def relabel(raw: dict, permutation: list[int]) -> dict:
    """permutation[old state] = new state; conjugate EVERY matrix."""
    n = raw["n"]
    if sorted(permutation) != list(range(n)):
        raise ValueError("not a permutation")
    old_at_new = [permutation.index(new) for new in range(n)]

    def conjugate(matrix):
        return [[matrix[old_at_new[i]][old_at_new[j]]
                 for j in range(n)] for i in range(n)]

    return {
        "n": n,
        "baseline": conjugate(raw["baseline"]),
        "descriptor": [raw["descriptor"][old_at_new[i]] for i in range(n)],
        "comparison": [permutation[i] for i in raw["comparison"]],
        "menu": [{"id": item["id"], "matrix": conjugate(item["matrix"])}
                 for item in raw["menu"]],
    }


def evaluate(raw: dict):
    r = execute(check_input(raw))
    assert verify_receipt(r)
    return r


class C10MetamorphicTests(unittest.TestCase):
    def assert_geometry_transported(self, old, new, perm):
        n = len(perm)
        self.assertEqual([new["event"][perm[i]] for i in range(n)], old["event"])
        pairs = {
            frozenset(cls): (idx, cls)
            for idx, cls in enumerate(new["classes"])
        }
        self.assertEqual(len(pairs), len(old["classes"]))
        for j, cls in enumerate(old["classes"]):
            moved = frozenset(perm[i] for i in cls)
            self.assertIn(moved, pairs)
            k, _ = pairs[moved]
            self.assertEqual(new["good"][k], old["good"][j])
            self.assertEqual(
                [new["absorption"][k][perm[i]] for i in range(n)],
                old["absorption"][j],
            )

    def assert_state_transport(self, original, perm):
        transformed = relabel(original, perm)
        a, b = evaluate(original), evaluate(transformed)
        self.assertEqual(a["optimum"], b["optimum"])
        self.assertEqual(a["selected"], b["selected"])
        self.assertEqual(a["ties"], b["ties"])
        self.assertEqual(
            [b["normalized_input"]["descriptor"][perm[i]]
             for i in range(original["n"])],
            a["normalized_input"]["descriptor"],
        )
        self.assertEqual(
            sorted(perm[i] for i in a["normalized_input"]["comparison"]),
            b["normalized_input"]["comparison"],
        )
        self.assert_geometry_transported(a["baseline"], b["baseline"], perm)
        comparison = a["normalized_input"]["comparison"]
        for old_member, new_member in zip(a["members"], b["members"]):
            self.assertEqual(old_member["id"], new_member["id"])
            self.assertEqual(old_member["margin"], new_member["margin"])
            self.assert_geometry_transported(
                old_member["geometry"], new_member["geometry"], perm)
            old_effects = dict(zip(comparison, old_member["effects"]))
            new_effects = dict(zip(b["normalized_input"]["comparison"],
                                   new_member["effects"]))
            self.assertEqual(
                {i: old_effects[i] for i in comparison},
                {i: new_effects[perm[i]] for i in comparison},
            )
            minimizers = [
                perm[i] for i in comparison
                if Q(old_effects[i]) == Q(old_member["margin"])
            ]
            self.assertEqual(new_member["worst_start"], min(minimizers))
        return a, b

    def test_01_six_state_nontrivial_relabel_all_classes(self):
        self.assert_state_transport(six_input(), [3, 5, 0, 2, 1, 4])

    def test_02_second_six_state_relabel(self):
        self.assert_state_transport(six_input(), [2, 1, 4, 0, 5, 3])

    def test_03_state_renaming_can_change_lowest_worst_start(self):
        a, b = self.assert_state_transport(six_input(), [3, 5, 0, 2, 1, 4])
        baseline_identity = next(z for z in a["members"] if z["id"] == "identity")
        moved_identity = next(z for z in b["members"] if z["id"] == "identity")
        self.assertEqual(baseline_identity["worst_start"], 1)
        self.assertEqual(moved_identity["worst_start"], 0)
        self.assertEqual(baseline_identity["margin"], moved_identity["margin"])

    def test_04_menu_permutation_preserves_each_indexed_score(self):
        original = six_input()
        a = evaluate(original)
        shifted = deepcopy(original)
        shifted["menu"] = [original["menu"][i] for i in [2, 4, 1, 5, 3, 0]]
        b = evaluate(shifted)
        self.assertEqual(a["optimum"], b["optimum"])
        self.assertEqual(a["selected"], b["selected"])
        self.assertEqual(a["ties"], b["ties"])
        self.assertEqual(
            [v["id"] for v in b["members"]],
            [original["menu"][i]["id"] for i in [2, 4, 1, 5, 3, 0]],
        )
        self.assertEqual(
            {z["id"]: (z["geometry"], z["effects"], z["margin"], z["worst_start"])
             for z in a["members"]},
            {z["id"]: (z["geometry"], z["effects"], z["margin"], z["worst_start"])
             for z in b["members"]},
        )

    def test_05_positive_maximizer_tie_tracks_declared_menu_order(self):
        original = six_input()
        full = deepcopy(original["menu"][0]["matrix"])
        identity = deepcopy(original["baseline"])
        original["menu"] = [
            {"id": "full-A", "matrix": full},
            {"id": "full-B", "matrix": full},
            {"id": "identity", "matrix": identity},
        ]
        a = evaluate(original)
        self.assertEqual((a["optimum"], a["selected"], a["ties"]),
                         ("1", "full-A", ["full-A", "full-B"]))
        reordered = deepcopy(original)
        reordered["menu"] = [original["menu"][1],
                             original["menu"][2], original["menu"][0]]
        b = evaluate(reordered)
        self.assertEqual((b["optimum"], b["selected"], b["ties"]),
                         ("1", "full-B", ["full-B", "full-A"]))
        self.assertEqual(
            {v["id"]: v["margin"] for v in a["members"]},
            {v["id"]: v["margin"] for v in b["members"]},
        )

    def test_06_all_zero_menu_still_selects_first_tie(self):
        original = six_input()
        identity = deepcopy(original["baseline"])
        original["menu"] = [
            {"id": "index-b", "matrix": identity},
            {"id": "index-a", "matrix": identity},
        ]
        a = evaluate(original)
        reordered = deepcopy(original)
        reordered["menu"].reverse()
        b = evaluate(reordered)
        self.assertEqual((a["optimum"], a["selected"], a["ties"]),
                         ("0", "index-b", ["index-b", "index-a"]))
        self.assertEqual((b["optimum"], b["selected"], b["ties"]),
                         ("0", "index-a", ["index-a", "index-b"]))
        self.assertEqual(a["numerical_status"], "NUMERIC_ALL_LISTED_MARGINS_ZERO")
        self.assertEqual(b["numerical_status"], "NUMERIC_ALL_LISTED_MARGINS_ZERO")

    def test_07_distinct_indices_identical_kernels_not_deduplicated(self):
        original = six_input()
        half = deepcopy(original["menu"][1]["matrix"])
        original["menu"] = [
            {"id": "candidate-one", "matrix": half},
            {"id": "candidate-two", "matrix": half},
        ]
        a = evaluate(original)
        self.assertEqual([v["id"] for v in a["members"]],
                         ["candidate-one", "candidate-two"])
        self.assertEqual(a["ties"], ["candidate-one", "candidate-two"])
        self.assertEqual(a["selected"], "candidate-one")


if __name__ == "__main__":
    unittest.main()
