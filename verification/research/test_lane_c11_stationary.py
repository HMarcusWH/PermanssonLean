"""Positive, negative and metamorphic C11 exact rational stationary tests."""
from __future__ import annotations

import copy
from fractions import Fraction
import json
import unittest

from c11_stationary_execution import (StationaryError, StationaryResourceLimit,
    execute, canonical_bytes, normalize_input, strict_loads)
from c11_verify_stationary import independent_classes, verify_report


def request(matrix, descriptor):
    return {"n": len(matrix), "matrix": matrix, "descriptor": descriptor}


class C11StationaryTests(unittest.TestCase):
    def test_01_one_state(self):
        out = execute(request([["1"]], [True]))
        self.assertTrue(verify_report(out))
        self.assertEqual(out["classes"], [
            {"states":[0], "stationary":["1"], "true_share":"1"}])

    def test_02_periodic_alternation(self):
        out = execute(request([["0","1"],["1","0"]], [False,True]))
        self.assertTrue(verify_report(out))
        self.assertEqual(out["classes"][0]["stationary"],["1/2","1/2"])
        self.assertEqual(out["classes"][0]["true_share"],"1/2")
        # This is NOT C10's eventually-always-true probability.
        from c10_exact_execution import class_values
        from fractions import Fraction as Q
        mat = ((Q(0), Q(1)), (Q(1), Q(0)))
        self.assertEqual(class_values(mat, (False, True))["event"], ["0", "0"])

    def test_03_asymmetric(self):
        out = execute(request([["2/3","1/3"],["1/4","3/4"]], [True,False]))
        self.assertTrue(verify_report(out))
        self.assertEqual(out["classes"][0]["stationary"],["3/7","4/7"])

    def test_04_two_absorbers_and_transient_split(self):
        out=execute(request([["0","1/3","2/3"],["0","1","0"],["0","0","1"]],
                            [False,True,False]))
        self.assertTrue(verify_report(out))
        self.assertEqual([r["states"] for r in out["classes"]], [[1],[2]])
        self.assertEqual([r["true_share"] for r in out["classes"]], ["1","0"])

    def test_05_six_state_baseline(self):
        from c10_golden import BASE
        out=execute(request(BASE,[False,False,True,True,True,True]))
        self.assertTrue(verify_report(out))
        self.assertEqual([(r["states"],r["stationary"],r["true_share"])
                          for r in out["classes"]], [
            ([2,3],["0","0","1/2","1/2","0","0"],"1"),
            ([4,5],["0","0","0","0","1/3","2/3"],"1")])

    def test_06_six_state_full_disruption(self):
        from c10_golden import six_input
        raw=six_input()
        out=execute(request(raw["menu"][0]["matrix"],raw["descriptor"]))
        self.assertTrue(verify_report(out))
        self.assertTrue(any(r["states"]==[1] and r["true_share"]=="0"
                            for r in out["classes"]))

    def test_07_forged_share_after_hash_repair(self):
        out=execute(request([["0","1"],["1","0"]], [False,True]))
        out["classes"][0]["true_share"]="1"
        with self.assertRaises(StationaryError):verify_report(out)

    def test_08_forged_balance_after_hash_repair(self):
        out=execute(request([["0","1"],["1","0"]], [False,True]))
        out["classes"][0]["stationary"]=["1/4","3/4"]
        with self.assertRaises(StationaryError):verify_report(out)

    def test_09_missing_extra_and_duplicate_classes(self):
        out=execute(request([["1","0"],["0","1"]], [False,True]))
        for mutate in [
          lambda r:r["classes"].pop(),
          lambda r:r["classes"].append(copy.deepcopy(r["classes"][0])),
          lambda r:r["classes"].reverse()]:
            bad=copy.deepcopy(out);mutate(bad)
            with self.assertRaises(StationaryError):verify_report(bad)

    def test_10_negative_offclass_and_wrong_mass(self):
        out=execute(request([["0","1/2","1/2"],["0","1","0"],["0","0","1"]],
                            [False,True,False]))
        for field, mutate in [
          ("negative", lambda v: v.__setitem__(1,"-1")),
          ("offclass", lambda v: v.__setitem__(0,"1/3")),
          ("badmass", lambda v: v.__setitem__(1,"1/2"))]:
            bad=copy.deepcopy(out);mutate(bad["classes"][0]["stationary"])
            with self.assertRaises(StationaryError,msg=field):verify_report(bad)

    def test_11_relabeling_transports_classes_and_shares(self):
        raw=request([["0","1/2","1/2"],["0","1","0"],["0","0","1"]],
                    [False,True,False])
        out=execute(raw)
        p=[2,0,1]
        changed=request([[raw["matrix"][p[i]][p[j]] for j in range(3)]
                         for i in range(3)], [raw["descriptor"][i] for i in p])
        other=execute(changed)
        self.assertTrue(verify_report(other))
        shares={tuple(sorted(r["states"])):r["true_share"] for r in out["classes"]}
        for r in other["classes"]:
            original=tuple(sorted(p[i] for i in r["states"]))
            self.assertEqual(r["true_share"],shares[original])
            for i in range(3):
                self.assertEqual(Fraction(r["stationary"][i]),
                  Fraction(next(c for c in out["classes"]
                                if tuple(c["states"])==original)["stationary"][p[i]]))

    def test_12_parser_rejects_float_duplicate_noncanonical(self):
        for raw in [b'{"n":1,"n":1,"matrix":[["1"]],"descriptor":[true]}',
                    b'{"n":1.0,"matrix":[["1"]],"descriptor":[true]}',
                    b'{"n":1,"matrix":[[NaN]],"descriptor":[true]}']:
            with self.assertRaises(StationaryError):strict_loads(raw)
        with self.assertRaises(StationaryError):
            normalize_input(request([["1/1"]],[True]))

    def test_13_zero_and_resource_limits(self):
        with self.assertRaises(StationaryError):
            normalize_input({"n":0,"matrix":[],"descriptor":[]})
        with self.assertRaises(StationaryResourceLimit):
            normalize_input(request([["1" if i==j else "0" for j in range(13)]
                                     for i in range(13)],[False]*13))

    def test_14_full_source_and_hash_binding(self):
        out=execute(request([["0","1"],["1","0"]], [False,True]))
        bad=copy.deepcopy(out)
        bad["normalized_input"]["descriptor"]=[True,True]
        with self.assertRaises(StationaryError):verify_report(bad)
        bad=copy.deepcopy(out)
        bad["claim_boundary"]="PROVED_EMPIRICAL_EXACT_GR"
        with self.assertRaises(StationaryError):verify_report(bad)

    def test_15_independent_dfs_matches_reference(self):
        from c11_stationary_execution import bottom_classes
        mats=[
         [[Fraction(1)]],
         [[Fraction(0),Fraction(1)],[Fraction(1),Fraction(0)]],
         [[Fraction(0),Fraction(1),Fraction(0)],
          [Fraction(0),Fraction(1),Fraction(0)],
          [Fraction(0),Fraction(0),Fraction(1)]]
        ]
        for mat in mats:
            self.assertEqual(independent_classes(mat),bottom_classes(mat))


    def test_16_same_length_duplicate_replaces_missing_class(self):
        out = execute(request([["1", "0"], ["0", "1"]], [False, True]))
        self.assertEqual(len(out["classes"]), 2)
        forged = copy.deepcopy(out)
        forged["classes"][1] = copy.deepcopy(forged["classes"][0])
        self.assertEqual(len(forged["classes"]), 2)
        with self.assertRaises(StationaryError):
            verify_report(forged)

if __name__=="__main__":
    unittest.main()
