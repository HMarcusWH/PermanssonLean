"""C10 exact mixed rational initial-law executor and cancellation tests."""
import copy
from fractions import Fraction as Q
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from c10_exact_execution import check_input, execute
from c10_golden import six_input
from c10_eval_initial_law import (
    eval_initial_law, parse_initial_law, InitialLawError, LAW_FORMAT,
)
from c10_verify_initial_law import verify_initial_report
from c10_verify_receipt import verify_receipt
from test_lane_c10_metamorphic import relabel


def law(weights):
    return {"format": LAW_FORMAT, "weights": weights}


class C10InitialLawTests(unittest.TestCase):
    def setUp(self):
        self.raw = six_input()
        self.receipt = execute(check_input(self.raw))
        self.half_half = law(["0", "1/2", "1/2", "0", "0", "0"])

    def test_01_six_state_half_half_exact(self):
        report = eval_initial_law(self.receipt, self.half_half)
        self.assertTrue(verify_initial_report(
            self.receipt, self.half_half, report))
        self.assertEqual(report["baseline_event"], "1")
        by_id = {x["id"]: x["event"] for x in report["members"]}
        self.assertEqual(by_id["full"], "0")
        self.assertEqual(by_id["half"], "1/4")
        self.assertEqual(by_id["tiny"], "999/2000")
        self.assertEqual(by_id["identity"], "1")
        self.assertEqual(by_id["u-only"], "1/2")
        self.assertEqual(by_id["b-only"], "1")

    def test_02_dirac_matches_actual_point_start(self):
        for index in range(6):
            w = ["1" if i == index else "0" for i in range(6)]
            report = eval_initial_law(self.receipt, law(w))
            self.assertEqual(report["baseline_event"],
                             self.receipt["baseline"]["event"][index])
            for a, b in zip(report["members"], self.receipt["members"]):
                self.assertEqual(a["event"], b["geometry"]["event"][index])

    def test_03_exact_signed_cancellation_not_original_margin(self):
        base = [["0", "0", "1", "0"], ["0", "0", "0", "1"],
                ["0", "0", "1", "0"], ["0", "0", "0", "1"]]
        modified = [["0", "0", "0", "1"], ["0", "0", "1", "0"],
                    ["0", "0", "1", "0"], ["0", "0", "0", "1"]]
        original = {"n": 4, "baseline": base,
                    "descriptor": [False, False, True, False],
                    "comparison": [0, 1],
                    "menu": [{"id": "swap", "matrix": modified}]}
        r = execute(check_input(original))
        report = eval_initial_law(r, law(["1/2", "1/2", "0", "0"]))
        self.assertTrue(verify_initial_report(
            r, law(["1/2", "1/2", "0", "0"]), report))
        self.assertEqual(r["members"][0]["comparison_effects"], ["1", "1"])
        self.assertEqual(r["members"][0]["margin"], "1")
        self.assertEqual(report["baseline_event"], "1/2")
        self.assertEqual(report["members"][0]["event"], "1/2")
        self.assertEqual(report["members"][0]["absolute_change"], "0")
        self.assertEqual(report["members"][0]["signed_change"], "0")

    def test_04_non_normalized_rejected(self):
        with self.assertRaises(InitialLawError):
            parse_initial_law(law(["1/2"] * 6), 6)

    def test_05_negative_rejected(self):
        with self.assertRaises(InitialLawError):
            parse_initial_law(law(["-1", "2", "0", "0", "0", "0"]), 6)

    def test_06_float_rejected(self):
        with self.assertRaises(InitialLawError):
            parse_initial_law(law([0.5, "1/2", "0", "0", "0", "0"]), 6)

    def test_07_wrong_dimension_rejected(self):
        with self.assertRaises(InitialLawError):
            parse_initial_law(law(["1"]), 6)

    def test_08_noncanonical_rational_rejected(self):
        with self.assertRaises(InitialLawError):
            parse_initial_law(law(["2/4", "1/2", "0", "0", "0", "0"]), 6)

    def test_09_wrong_weight_digest_rejected(self):
        report = eval_initial_law(self.receipt, self.half_half)
        report["initial_sha256"] = "0" * 64
        with self.assertRaises(InitialLawError):
            verify_initial_report(self.receipt, self.half_half, report)

    def test_10_wrong_member_rejected(self):
        report = eval_initial_law(self.receipt, self.half_half)
        report["members"][0]["event"] = "1/7"
        with self.assertRaises(InitialLawError):
            verify_initial_report(self.receipt, self.half_half, report)

    def test_11_mixed_query_does_not_change_original_score(self):
        before = [(x["id"], x["margin"], x["worst_start"])
                  for x in self.receipt["members"]]
        eval_initial_law(self.receipt, self.half_half)
        after = [(x["id"], x["margin"], x["worst_start"])
                 for x in self.receipt["members"]]
        self.assertEqual(before, after)

    def test_12_relabel_initial_weight_transport(self):
        perm = [3, 5, 0, 2, 1, 4]
        new_raw = relabel(self.raw, perm)
        new_receipt = execute(check_input(new_raw))
        moved = ["0"] * 6
        for i, w in enumerate(self.half_half["weights"]):
            moved[perm[i]] = w
        first = eval_initial_law(self.receipt, self.half_half)
        second = eval_initial_law(new_receipt, law(moved))
        self.assertEqual(first["baseline_event"], second["baseline_event"])
        self.assertEqual(
            {x["id"]: x["event"] for x in first["members"]},
            {x["id"]: x["event"] for x in second["members"]},
        )
        self.assertTrue(verify_initial_report(new_receipt, law(moved), second))

    def test_13_legacy_receipt_rejected(self):
        old = execute(check_input(self.raw), format_version=1)
        self.assertTrue(verify_receipt(old))
        with self.assertRaises(InitialLawError):
            eval_initial_law(old, self.half_half)

    def test_14_cli_evaluator_and_verifier(self):
        with tempfile.TemporaryDirectory() as t:
            root = Path(t)
            (root / "receipt.json").write_text(json.dumps(self.receipt))
            (root / "law.json").write_text(json.dumps(self.half_half))
            producer = Path(__file__).with_name("c10_eval_initial_law.py")
            checker = Path(__file__).with_name("c10_verify_initial_law.py")
            x = subprocess.run([sys.executable, str(producer), str(root/"receipt.json"),
                                str(root/"law.json"), "-o", str(root/"report.json")],
                               capture_output=True, text=True)
            self.assertEqual(x.returncode, 0, x.stdout+x.stderr)
            y = subprocess.run([sys.executable, str(checker), str(root/"receipt.json"),
                                str(root/"law.json"), str(root/"report.json")],
                               capture_output=True, text=True)
            self.assertEqual(y.returncode, 0, y.stdout+y.stderr)


if __name__ == "__main__":
    unittest.main()
