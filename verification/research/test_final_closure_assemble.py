"""Exact-source candidate assembly cannot invent CI IDs or review approvals."""
import json
from pathlib import Path
import tempfile
import unittest
from unittest import mock

import final_closure_assemble as a
import final_closure_authenticate as auth


class AssemblyTests(unittest.TestCase):
    def test_mocked_green_head_still_yields_zero_accepted_claims(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            comp = root / "compiler.json"
            mutations = root / "mutations.json"
            bundle = root / "evidence.zip"
            comp.write_text(json.dumps({
                "head_sha": "a"*40,
                "status": "COMPILER_ONLY_UNREVIEWED",
                "compiler_axiom_receipts": [{
                    "id": "p1", "head_sha": "a"*40,
                    "compiler_result": "PASS",
                    "path": "PermanssonResearch/Simple.lean",
                    "declaration": "Example.foo",
                    "source_sha256": "0"*64,
                    "statement_sha256": "1"*64,
                    "elaborated_type_sha256": "3"*64,
                    "declaration_kind": "theorem",
                    "universe_params_repr": "[]",
                    "transitive_axioms": [],
                    "compiler_check": "research",
                    "axiom_log_sha256": "2"*64,
                    "case_ids": ["Q-05"], "claim_ids": ["Q1"],
                    "axiom_log_member": "axiom_logs/p1.log",
                    "check_run_id": None,
                    "CI_binding": "PENDING_REAL_CHECK_RUN_ID_ON_FROZEN_H",
                    "independent_review": "NOT_RECEIVED",
                }],
            }))
            mutations.write_text("[]")
            bundle.write_bytes(b"mock source bundle")
            def git(*args):
                if args == ("rev-parse", "HEAD"):
                    return "a"*40
                if args[:2] == ("cat-file", "-t"):
                    return "commit"
                if args[:3] == ("show", "-s", "--format=%P"):
                    return auth.BASE + " " + "a"*40
                if args[:1] == ("rev-parse",):
                    return "f"*40
                raise AssertionError("unhandled git read")
            checks = {
                key: {"id": idx+1, "head_sha": "a"*40}
                for idx, key in enumerate(sorted(auth.REQUIRED))}
            with mock.patch.object(a, "git", side_effect=git), \
                 mock.patch.object(a, "authenticated_checks", return_value=checks), \
                 mock.patch.object(a, "load_detached_bundle",
                                   return_value={"axiom_logs/p1.log": b"proof"}):
                value = a.assemble("a"*40, "b"*40,
                                   compiler_candidate=comp,
                                   mutation_candidates=mutations,
                                   bundle=bundle)
            self.assertEqual(value["format"],
                             "Permansson.FinalClosureDetachedReceipts.v2")
            self.assertEqual(value["case_decisions"], [])
            self.assertEqual(value["claim_decisions"], [])
            self.assertEqual(value["independent_source_reviews"], [])
            self.assertIsNone(value["compiler_axiom_receipts"][0]["check_run_id"])
            self.assertTrue(value["source_bound_ci"])

    def test_wrong_synthetic_parents_fail_before_evidence_promotion(self):
        with tempfile.TemporaryDirectory() as folder:
            root = Path(folder)
            for name in ("compiler.json", "mutation.json"):
                (root/name).write_text("{}")
            (root/"bundle.zip").write_bytes(b"garbage")
            def bogus(*args):
                if args == ("rev-parse", "HEAD"):
                    return "a"*40
                if args[:2] == ("cat-file", "-t"):
                    return "commit"
                if args[:3] == ("show", "-s", "--format=%P"):
                    return "wrong" + " " + "a"*40
                return "0"*40
            with mock.patch.object(a, "git", side_effect=bogus):
                with self.assertRaises(auth.AuthenticationError):
                    a.assemble("a"*40, "b"*40,
                               compiler_candidate=root/"compiler.json",
                               mutation_candidates=root/"mutation.json",
                               bundle=root/"bundle.zip")


if __name__ == "__main__":
    unittest.main()
