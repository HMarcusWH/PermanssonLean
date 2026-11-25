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
from verification.research.approx_equilibrium.contract import FORMAT, Invalid, parse, pack
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

def asymmetric():
    # Player two's OWN action controls the next state. If its P is not
    # transposed along with C, the first state's second score is wrong.
    return dict(format=FORMAT,kind="discounted",states=2,
                R=[[["0","0"],["0","0"]]]*2,
                C=[[["0","0"],["0","0"]]]*2,
                P=[[[["1","0"],["0","1"]],[["1","0"],["0","1"]]]]*2,
                x=[["1","0"]]*2,y=[["1","0"]]*2,
                discount=["1/2","1/2"],values=[["0","0"],["0","1"]])

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

    def test_AE_T33_asymmetric_player_two(self):
        r=verified(asymmetric())
        self.assertEqual(r["evaluations"][0]["column_scores"],["0","1/2"])
        self.assertEqual(r["epsilon"],["0","1/2"])
        self.assertEqual(r["rho"],["0","1"])
    def test_AE_T34_normalization_units(self):
        r=verified(asymmetric())
        self.assertEqual(r["normalized"][0]["widths"],["0","1/2"])
        self.assertEqual(r["normalized"][0]["regret"],["0","1"])
        self.assertEqual(r["full_history_bound"][1],"5")
    def test_AE_T35_constant_continuation(self):
        d=asymmetric();d["values"]=[["0","0"],["0","0"]]
        r=verified(d)
        self.assertEqual(r["normalized"],[{"widths":["0","0"],"regret":["0","0"]}]*2)
    def test_AE_T36_all_tied_projection_is_identity(self):
        d=fixture("matching");r=verified(d)
        for i,k in enumerate(("x","y")):
            self.assertEqual(r["fixed_opponent_projection"][i]["projection"],d[k])
    def test_AE_T37_equal_marginals_different_correlations(self):
        p=(Q(1,2),Q(0),Q(0),Q(1,2));q=(Q(0),Q(1,2),Q(1,2),Q(0))
        self.assertEqual((p[0]+p[1],p[0]+p[2]),(q[0]+q[1],q[0]+q[2]))
        self.assertEqual(sum(abs(a-b) for a,b in zip(p,q))/2,1)
        d=fixture("transport");d["joint_action"]=[str(a) for a in p]
        with self.assertRaises(Invalid):parse(d)
    def test_AE_T38_two_nonzero_budget_arithmetic(self):
        # General two-budget theorem regression; the narrow CLI deliberately
        # does not allow a different replacement on the two sides.
        baseline=abs(Q(1)-Q(0));approx=abs(Q(9,10)-Q(1,10))
        self.assertEqual(baseline-approx,Q(1,5))
        self.assertGreater(baseline-approx,Q(1,10))
        self.assertEqual(baseline-approx,Q(1,10)+Q(1,10))
    def test_AE_T39_omitted_tied_start(self):
        d=fixture("transport");d["region"]=[0,1,2];d["comparison"]=[0,1,2]
        r=candidate(d);short=copy.deepcopy(d);short["comparison"]=[0,1]
        self.assertEqual(verified(short)["finite_margin"],r["result"]["finite_margin"])
        with self.assertRaises(Invalid):check(short,r)
    def test_AE_T40_verified_but_threshold_not_met(self):
        d=dominant("1/4");d["epsilon"]="1/5"
        r=candidate(d);v=check(d,r)
        self.assertEqual(v["numeric_status"],"VERIFIED_EXACT_RATIONAL")
        self.assertEqual(v["disposition"],"THRESHOLD_NOT_MET")
    def test_AE_T41_tampered_kite_weight(self):
        d=fixture("kite");r=candidate(d);r["result"]["weight"]="1/10"
        with self.assertRaises(Invalid):check(d,r)
    def test_AE_T42_tampered_projection(self):
        d=dominant("1/10");r=candidate(d)
        r["result"]["fixed_opponent_projection"][0]["projection"]=["0","1"]
        with self.assertRaises(Invalid):check(d,r)
    def test_AE_T43_tampered_scale(self):
        d=asymmetric();r=candidate(d);r["result"]["normalized"][0]["widths"][1]="1"
        with self.assertRaises(Invalid):check(d,r)
    def test_AE_T44_changed_physical_transition(self):
        d=fixture("transport");r=candidate(d);d["P"][0][0][0]=["0","1","0"]
        with self.assertRaises(Invalid):check(d,r)
    def test_AE_T45_arithmetic_preflight_and_result_limit(self):
        d=fixture("matching")
        d["R"][0][0]=str(Q(1,(1<<191)-1))
        d["R"][0][1]=str(Q(1,(1<<191)-3))
        with self.assertRaises(Invalid):parse(d)
        with self.assertRaises(Invalid):pack(Q(1<<14001))
    def test_noncanonical_rational(self):
        d=fixture("matching");d["x"]=["2/4","1/2"]
        with self.assertRaises(Invalid):parse(d)

if __name__=="__main__":unittest.main()
