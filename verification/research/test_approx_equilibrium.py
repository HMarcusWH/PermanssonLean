"""Exact fixtures and adversarial controls for the additive research lane."""
import copy
import json
from pathlib import Path
import sys
import unittest
from fractions import Fraction as Q

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT))
from verification.research.approx_equilibrium.__main__ import candidate
from verification.research.approx_equilibrium.checker import check
from verification.research.approx_equilibrium.contract import FORMAT, Invalid, parse
from permansson_app.errors import AppError

FIXTURES=json.loads((Path(__file__).parent/"approx_equilibrium/fixtures.json").read_text())

def fixture(name):
    return copy.deepcopy(FIXTURES[name])

def verified(raw):
    r=candidate(raw)
    assert check(raw,r)["numeric_status"]=="VERIFIED_EXACT_RATIONAL"
    return r["result"]

def dominant(e="0"):
    return dict(format=FORMAT,kind="regret",R=[["1","1"],["0","0"]],
                C=[["1","0"],["1","0"]],x=[str(1-Q(e)),e],y=["1","0"],epsilon=e)

class ExactEquilibriumTests(unittest.TestCase):
    def test_AE_T01_matching_pennies(self):
        r=verified(fixture("matching")); self.assertEqual(r["regret"],["0","0"])
    def test_AE_T02_coordination_strict(self):
        d=fixture("matching");d["C"]=d["R"]
        for p in (["1","0"],["0","1"]):
            d["x"]=p;d["y"]=p
            r=verified(d);self.assertTrue(r["exact_nash"])
            self.assertEqual(r["fixed_opponent_projection"][0]["gap"],"1")
    def test_AE_T03_rectangular(self):
        d=fixture("matching");d.update(R=[["0","1","0"],["0","0","1"]],C=[["0","1","0"],["0","0","1"]],x=["0","1"],y=["0","0","1"])
        self.assertTrue(verified(d)["exact_nash"])
    def test_AE_T04_single_action(self):
        d=fixture("matching");d.update(R=[["0"]],C=[["1"]],x=["1"],y=["1"])
        self.assertTrue(verified(d)["exact_nash"])
    def test_AE_T05_ties_complete(self):
        r=verified(fixture("matching"));self.assertEqual(r["best_responses"],[[0,1],[0,1]])
    def test_AE_T06_normalization(self):
        d=fixture("matching");d["x"]=["1","1"]
        with self.assertRaises(Invalid):parse(d)
    def test_AE_T07_negative_probability(self):
        d=fixture("matching");d["x"]=["-1","2"]
        with self.assertRaises(AppError):parse(d)
    def test_AE_T08_payoff_scale(self):
        d=fixture("matching");d["R"][0][0]="2"
        with self.assertRaises(AppError):parse(d)
    def test_AE_T09_threshold_equality(self):
        r=verified(dominant("1/5"));self.assertTrue(r["threshold_met"]);self.assertEqual(r["regret"],["1/5","0"])
    def test_AE_T10_threshold_exceeded(self):
        d=dominant("1/4");d["epsilon"]="1/5"
        self.assertFalse(verified(d)["threshold_met"])
    def test_AE_T11_kite_boundary(self):
        r=verified(fixture("kite"));self.assertEqual(r["kite_lhs"][0],"1/5")
    def test_AE_T12_outside_kite(self):
        d=fixture("kite");d["x"]=["1/2","1/2"]
        r=verified(d);self.assertEqual(r["branch"],"OUTSIDE_KITE");self.assertIsNone(r["output"])
    def test_AE_T13_row_mix(self):
        r=verified(fixture("kite"));self.assertEqual(r["branch"],"ROW")
        self.assertEqual(r["weight"],"1/5");self.assertEqual(r["output"]["x"],["4/5","1/5"])
        self.assertEqual(r["output"]["evaluation"]["regret"],["1/5","0"])
    def test_AE_T14_column_mix(self):
        d=fixture("kite");d.update(R=[["0","0"],["0","0"]],C=[["1","0"],["1","0"]],x=["1","0"],y=["3/4","1/4"])
        r=verified(d);self.assertEqual(r["branch"],"COLUMN");self.assertEqual(r["output"]["y"],["4/5","1/5"])
    def test_AE_T15_unchanged(self):
        d=fixture("matching");d.update(kind="kite",epsilon="1/5")
        self.assertEqual(verified(d)["branch"],"UNCHANGED")
    def test_AE_T16_x1(self):
        r=verified(fixture("x1"));self.assertEqual(r["epsilon"],["0","0"]);self.assertEqual(r["rho"],["0","0"])
        self.assertEqual(r["full_history_bound"],["0","0"])
        e=r["evaluations"][0];self.assertEqual(Q(e["row_scores"][0])-Q(e["row_scores"][1]),Q(9,211))
        self.assertEqual(Q(e["column_scores"][0])-Q(e["column_scores"][1]),Q(9,211))
    def test_AE_T17_nonzero_residual(self):
        d=fixture("x1");d["values"]=[["0","0"],["0","0"]]
        r=verified(d);self.assertTrue(any(Q(a)>0 for a in r["rho"]))
        for i in range(2):
            self.assertEqual(Q(r["full_history_bound"][i]),(Q(r["epsilon"][i])+2*Q(r["rho"][i]))/Q(1,10))
    def test_AE_T18_value_tamper(self):
        d=fixture("x1");r=candidate(d);d["values"][0][0]="0"
        with self.assertRaises(Invalid):check(d,r)
    def test_AE_T19_zero_discount(self):
        d=fixture("x1");d["discount"]=["0","0"]
        r=verified(d);self.assertEqual(r["continuation"],[d["R"],d["C"]])
    def test_AE_T20_near_one_discount(self):
        d=fixture("x1");d["discount"]=["99/100","99/100"]
        r=verified(d)
        for i in range(2):self.assertEqual(Q(r["full_history_bound"][i]),100*(Q(r["epsilon"][i])+2*Q(r["rho"][i])))
        d["discount"][0]="1"
        with self.assertRaises(Invalid):parse(d)
    def test_AE_T21_gap_projection(self):
        r=verified(dominant("1/10"));p=r["fixed_opponent_projection"][0]
        self.assertEqual(p["tv"],"1/10");self.assertEqual(p["bound"],"1/10")
        self.assertEqual(p["projection"],["1","0"])
    def test_AE_T22_all_tied(self):
        p=verified(fixture("matching"))["fixed_opponent_projection"][0]
        self.assertIsNone(p["gap"]);self.assertEqual(p["tv"],"0")
    def test_AE_T23_opponent_change(self):
        d=fixture("matching");r=candidate(d);d["y"]=["1","0"]
        with self.assertRaises(Invalid):check(d,r)
    def test_AE_T24_product_budget(self):
        d=fixture("transport");d["y_tilde"]=[["9/10","1/10"]]*3
        r=verified(d);self.assertEqual(r["baseline_kernel_budget"],"19/100")
        self.assertEqual(r["approximate_finite_margin"],str(Q(81,100)**3))
    def test_AE_T25_no_correlated_substitution(self):
        d=fixture("transport");d["joint_action"]=[["1","0","0","0"]]*3
        with self.assertRaises(Invalid):parse(d)
    def test_AE_T26_sharp_transport(self):
        r=verified(fixture("transport"))
        for k,v in {"baseline_path_budget":"271/1000","intervention_path_budget":"0",
                    "finite_margin":"1","approximate_finite_margin":"729/1000",
                    "margin_lower_bound":"729/1000"}.items():self.assertEqual(r[k],v)
    def test_AE_T27_omitted_error_receipt(self):
        d=fixture("transport");r=candidate(d);del r["result"]["intervention_path_budget"]
        with self.assertRaises(Invalid):check(d,r)
    def test_AE_T28_horizon_zero(self):
        d=fixture("transport");d["horizon"]=0
        r=verified(d);self.assertEqual(r["baseline_path_budget"],"0");self.assertEqual(r["finite_margin"],"0")
    def test_AE_T29_recurring_leak(self):
        for den in (10,100,1000):
            d=fixture("transport");p=Q(1,den);d["x_tilde"]=[[str(1-p),str(p)]]*3;d["horizon"]=16
            r=verified(d)
            self.assertEqual(Q(r["approximate_finite_margin"]),(1-p)**16)
            self.assertLess(Q(r["approximate_finite_margin"]),1)
            self.assertFalse(check(d,candidate(d))["original_regime_certificate"])
    def test_AE_T30_strict_equilibria_opposite_survival(self):
        d=fixture("transport");d["x_tilde"]=[["0","1"]]*3;d["y_tilde"]=[["0","1"]]*3
        r=verified(d);self.assertEqual(r["baseline_survival"],["1","1","0"])
        self.assertEqual(r["approximate_survival"],["0","0","0"])
    def test_foreign_receipt(self):
        d=fixture("matching");r=candidate(d);r["input_sha256"]="0"*64
        with self.assertRaises(Invalid):check(d,r)
    def test_tampered_exact_payoff(self):
        d=fixture("matching");r=candidate(d);r["result"]["payoff"][0]="0"
        with self.assertRaises(Invalid):check(d,r)
    def test_numeric_boolean_substitution(self):
        d=fixture("matching");r=candidate(d);r["result"]["exact_nash"]=1
        with self.assertRaises(Invalid):check(d,r)
    def test_omitted_comparison_start(self):
        d=fixture("transport");d["comparison"]=[0]
        with self.assertRaises(Invalid):parse(d)
    def test_resource_scope(self):
        d=fixture("transport");d["horizon"]=17
        with self.assertRaises(Invalid):parse(d)
    def test_invalid_number_wire_type(self):
        d=fixture("matching");d["x"]=[0.5,0.5]
        with self.assertRaises(AppError):parse(d)

if __name__=="__main__":unittest.main()
