"""Selection survey adversaries; synthetic maps are never reviewed choices."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

import pr113_selection_candidate_survey as survey
from pr113_v31_execution_integrity import CLAIMS

H = "a" * 40
ROUTES = "verification/research/test_fixture_routes.py"
CLAIM_TESTS = "verification/research/test_fixture_claims.py"
CASE_IDS = [f"C-{i:02}" for i in range(1, 46)]


def method(cid):
    return "test_" + cid.replace("-", "").lower()


def proof(owner):
    return "PermanssonResearch/Fixture/" + owner.replace("-", "") + ".lean"


def test_source(classes):
    body = ""
    for cls, names in classes.items():
        body += f"class {cls}:\n" + "".join(
            f"    def {n}(self):\n        pass\n" for n in names)
    return body.encode()


def fixture():
    cases = {"format": "fixture", "status": "UNREVIEWED", "cases": [{
        "case_id": c,
        "test_method_candidates": [
            {"path": ROUTES, "method": method(c), "role": "COMPILER_SOURCE"},
            {"path": ROUTES, "method": method(c) + "_false",
             "role": "SEMANTIC_NEGATIVE"},
        ],
        "historical_proof_declarations": [{"path": proof(c), "name": "t"}],
    } for c in CASE_IDS]}
    claims = {"format": "fixture", "status": "UNREVIEWED",
              "count": len(CLAIMS), "claims": [{
                  "claim_id": c, "primary_path": proof(c),
                  "declarations": [{"path": proof(c), "declaration": "d"}],
                  "test_source_candidates": [CLAIM_TESTS],
                  "original_case_links": ["C-01"],
              } for c in sorted(CLAIMS)]}
    blobs = {
        ROUTES: test_source({"Routes": [
            n for c in CASE_IDS for n in (method(c), method(c) + "_false")]}),
        CLAIM_TESTS: test_source({"Claims": [
            "test_" + c.lower() + side for c in sorted(CLAIMS)
            for side in ("_true", "_false")]}),
        **{proof(c): b"theorem t : True := trivial\n" for c in CASE_IDS},
        **{proof(c): b"theorem d : True := trivial\n" for c in CLAIMS},
    }
    return cases, claims, blobs


def run(cases, claims, blobs):
    encode = lambda value: (json.dumps(value) + "\n").encode()
    return survey.build_survey(H, encode(cases), encode(claims), blobs.get)


class SelectionSurveyTests(unittest.TestCase):
    def test_complete_survey_is_deterministic_and_unreviewed(self):
        cases, claims, blobs = fixture()
        report = run(cases, claims, blobs)
        self.assertEqual(report, run(*fixture()))
        self.assertEqual(report["status"], "UNREVIEWED_SURVEY_COVERAGE_COMPLETE")
        self.assertEqual(report["summary"]["original_cases"], 45)
        self.assertEqual(report["summary"]["claims"], 11)
        for field in ("selection_written", "independent_review",
                      "mathematical_relevance_established"):
            self.assertIs(report[field], False)
        self.assertEqual(report["accepted_cases"], 0)
        self.assertEqual(report["accepted_claims"], 0)
        self.assertEqual(report["cases"][0]["positive_routes"][0]
                         ["defining_classes"], ["Routes"])
        for claim in report["claims"]:
            self.assertIsNone(claim["negative_lean_statement"])
            self.assertIn("POSITIVE_AND_NEGATIVE_TEST_METHODS_REQUIRE_REVIEW",
                          claim["flags"])
            self.assertIn("FALSE_LEAN_STATEMENT_NOT_PROVIDED", claim["flags"])
            self.assertIn("TEST_SOURCE_SHARED_WITH_OTHER_CLAIMS", claim["flags"])
        self.assertEqual(report["summary"]["claims_sharing_test_sources"],
                         sorted(CLAIMS))
        self.assertIn("UNREVIEWED", survey.markdown(report))

    def test_claim_specific_test_source_is_not_flagged_shared(self):
        cases, claims, blobs = fixture()
        own = "verification/research/test_fixture_q1.py"
        claims["claims"][[c["claim_id"] for c in claims["claims"]]
                         .index("Q1")]["test_source_candidates"] = [own]
        blobs[own] = test_source({"Q1": ["test_q1_true", "test_q1_false"]})
        report = run(cases, claims, blobs)
        q1 = next(c for c in report["claims"] if c["claim_id"] == "Q1")
        self.assertNotIn("TEST_SOURCE_SHARED_WITH_OTHER_CLAIMS", q1["flags"])
        self.assertEqual(q1["test_sources"][0]["shared_with_claims"], [])
        self.assertNotIn("Q1", report["summary"]["claims_sharing_test_sources"])

    def test_multiple_eligible_routes_are_flagged_not_chosen(self):
        cases, claims, blobs = fixture()
        cases["cases"][1]["test_method_candidates"].append({
            "path": ROUTES, "method": method("C-03"), "role": "EXACT_CHECK"})
        report = run(cases, claims, blobs)
        self.assertEqual(
            report["summary"]["cases_with_multiple_eligible_positive_routes"],
            ["C-02"])
        self.assertEqual(report["cases"][1]["eligible_positive_route_count"], 2)

    def test_missing_or_duplicate_case_owner_fails_closed(self):
        for name, edit in (
            ("missing", lambda c: c["cases"].pop()),
            ("duplicate", lambda c: c["cases"].__setitem__(
                1, dict(c["cases"][0]))),
            ("malformed", lambda c: c["cases"][0].__setitem__(
                "case_id", "../C-01")),
            ("untyped", lambda c: c["cases"][0].__setitem__("case_id", 1)),
        ):
            with self.subTest(fault=name):
                cases, claims, blobs = fixture()
                edit(cases)
                with self.assertRaises(survey.SurveyError):
                    run(cases, claims, blobs)

    def test_missing_duplicate_or_foreign_claim_owner_fails_closed(self):
        for name, edit in (
            ("missing", lambda c: c["claims"].pop()),
            ("duplicate", lambda c: c["claims"].__setitem__(
                1, dict(c["claims"][0]))),
            ("foreign", lambda c: c["claims"][0].__setitem__(
                "claim_id", "Z9")),
            ("count", lambda c: c.__setitem__("count", 12)),
        ):
            with self.subTest(fault=name):
                cases, claims, blobs = fixture()
                edit(claims)
                with self.assertRaises(survey.SurveyError):
                    run(cases, claims, blobs)

    def test_foreign_providers_and_links_fail_closed(self):
        for name, edit in (
            ("case-provider-outside-lean-roots", lambda c, k: c["cases"][0]
                ["historical_proof_declarations"][0].__setitem__(
                    "path", "verification/research/Fixture.lean")),
            ("case-provider-escape", lambda c, k: c["cases"][0]
                ["historical_proof_declarations"][0].__setitem__(
                    "path", "PermanssonResearch/../Fixture.lean")),
            ("claim-primary-not-declared", lambda c, k: k["claims"][0]
                .__setitem__("primary_path", proof("C-01"))),
            ("claim-foreign-case-link", lambda c, k: k["claims"][0]
                .__setitem__("original_case_links", ["Z-99"])),
            ("foreign-test-path", lambda c, k: c["cases"][0]
                ["test_method_candidates"][0].__setitem__(
                    "path", "verification/integrity/tests/test_x.py")),
            ("unknown-role", lambda c, k: c["cases"][0]
                ["test_method_candidates"][0].__setitem__("role", "ACCEPTED")),
        ):
            with self.subTest(fault=name):
                cases, claims, blobs = fixture()
                edit(cases, claims)
                with self.assertRaises(survey.SurveyError):
                    run(cases, claims, blobs)

    def test_absent_method_is_ineligible_and_coverage_incomplete(self):
        cases, claims, blobs = fixture()
        blobs[ROUTES] = blobs[ROUTES].replace(
            b"def " + method("C-04").encode() + b"(", b"def renamed(")
        report = run(cases, claims, blobs)
        case = report["cases"][3]
        self.assertEqual(case["positive_routes"][0]["status"], "ABSENT_METHOD")
        self.assertIn("NO_ELIGIBLE_POSITIVE_ROUTE", case["flags"])
        self.assertEqual(report["status"],
                         "UNREVIEWED_SURVEY_COVERAGE_INCOMPLETE")
        self.assertEqual(
            report["summary"]["cases_without_complete_coverage"], ["C-04"])

    def test_ambiguous_class_and_absent_sources_are_incomplete(self):
        cases, claims, blobs = fixture()
        blobs[ROUTES] += test_source({"Other": [method("C-05")]})
        del blobs[proof("C-06")]
        del blobs[CLAIM_TESTS]
        report = run(cases, claims, blobs)
        self.assertEqual(report["cases"][4]["positive_routes"][0]["status"],
                         "AMBIGUOUS_CLASS")
        self.assertIn("NO_LEAN_PROVIDER_AT_HEAD", report["cases"][5]["flags"])
        self.assertEqual(report["summary"]["cases_without_complete_coverage"],
                         ["C-05", "C-06"])
        self.assertEqual(report["summary"]["claims_without_complete_coverage"],
                         sorted(CLAIMS))

    def test_exact_head_cli_writes_only_detached_unreviewed_survey(self):
        head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=survey.ROOT,
                              capture_output=True, text=True).stdout.strip()
        with tempfile.TemporaryDirectory() as temporary:
            inside = survey.ROOT / "selection-survey-must-not-exist"
            self.assertEqual(survey.main(["--head", head,
                                          "--out", str(inside)]), 2)
            self.assertFalse(inside.exists())
            reviewed = Path(temporary) / "reviewed_positive45_selection_v31"
            self.assertEqual(survey.main(["--head", head,
                                          "--out", str(reviewed)]), 2)
            self.assertEqual(survey.main(["--head", "b" * 40, "--out",
                                          str(Path(temporary) / "stale")]), 2)
            out = Path(temporary) / "survey"
            self.assertIn(survey.main(["--head", head, "--out", str(out)]),
                          (0, 1))
            self.assertEqual(sorted(p.name for p in out.iterdir()),
                             [survey.JSON_NAME, survey.MARKDOWN_NAME])
            report = json.loads((out / survey.JSON_NAME).read_text())
            self.assertEqual(report["source_head"], head)
            self.assertEqual(report["summary"]["original_cases"], 45)
            self.assertEqual(report["summary"]["claims"], 11)
            self.assertIs(report["independent_review"], False)
            self.assertEqual(report["accepted_cases"], 0)


if __name__ == "__main__":
    unittest.main()
