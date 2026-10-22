"""Adversarial logic tests; synthetic fixtures are NOT genuine GitHub reviews."""
import copy
import hashlib
from pathlib import Path
import stat
import tempfile
import unittest
from unittest import mock
import zipfile

import final_closure_case_receipts as gate
from closure_elaborated_type import elaborated_type_sha256

H = "a" * 40
sha = lambda raw: hashlib.sha256(raw).hexdigest()


class DetachedCaseReceiptTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="perm-case-")
        self.addCleanup(self.tmp.cleanup)
        root = Path(self.tmp.name)
        self.repo = root / "repo"
        self.repo.mkdir()
        (self.repo / "Proof.lean").write_text(
            "namespace Test.Scope\n"
            "theorem genuine : True := by trivial\n"
            "end Test.Scope\n")
        (self.repo / "test_actual.py").write_text(
            "def test_meaningful_mutant():\n    assert True\n")
        self.logs = {
            "axiom.log": (
                b"PERMANSSON_ELABORATED_TYPE_V1_BEGIN\n"
                b"NAME=Test.Scope.genuine\nKIND=theorem\nUNIVERSES=[]\n"
                b"TYPE=Expr.const `True []\n"
                b"PERMANSSON_ELABORATED_TYPE_V1_END\n"
                b"Test.Scope.genuine depends on axioms: []\n"),
            "positive.log": b"test_meaningful_mutant ... ok\n",
            "negative.log": b"Test.Scope.genuine: error: unsolved goals\n",
            "mutant.lean": b"namespace Test.Scope\ntheorem genuine : False := by trivial\nend Test.Scope\n",
        }
        self.bundle = root / "evidence.zip"
        self.save()
        self.checks = {"research": {"id": 42, "head_sha": H}}
        self.proof = {
            "id": "p", "head_sha": H, "path": "Proof.lean",
            "declaration": "Test.Scope.genuine",
            "source_sha256": sha((self.repo / "Proof.lean").read_bytes()),
            "statement_sha256": sha(b"theorem genuine : True"),
            "elaborated_type_sha256": elaborated_type_sha256({
                "declaration": "Test.Scope.genuine",
                "declaration_kind": "theorem",
                "universe_params_repr": "[]",
                "type_expr_repr": "Expr.const `True []",
            }),
            "declaration_kind": "theorem",
            "universe_params_repr": "[]",
            "transitive_axioms": [], "compiler_check": "research",
            "compiler_result": "PASS", "check_run_id": 42,
            "axiom_log_member": "axiom.log",
            "axiom_log_sha256": sha(self.logs["axiom.log"]),
            "case_ids": ["C-01"], "claim_ids": ["Q1"],
        }
        self.test = {
            "id": "t", "head_sha": H, "test_path": "test_actual.py",
            "test_name": "test_meaningful_mutant",
            "source_sha256": sha((self.repo / "test_actual.py").read_bytes()),
            "case_ids": ["C-01"], "check_run_id": 42,
            "positive_control": {"compiled": True, "exit_code": 0,
                "lean_toolchain": "4.34.0", "log_member": "positive.log",
                "log_sha256": sha(self.logs["positive.log"])},
            "log_member": "positive.log",
            "log_sha256": sha(self.logs["positive.log"]),
            "outcome": "PASS", "compiler_exit_code": 0,
        }
        self.negative = dict(self.test,
            id="n", log_member="negative.log",
            log_sha256=sha(self.logs["negative.log"]),
            mutant_source_sha256=sha(self.logs["mutant.lean"]),
            mutant_source_member="mutant.lean",
            original_lean_source_path="Proof.lean",
            original_lean_source_sha256=sha((self.repo/"Proof.lean").read_bytes()),
            outcome="REJECTED_SEMANTIC", compiler_exit_code=1)
        self.ledger = {"cases": [
            {"case_id": "C-%02d" % i,
             "required_expected_result": "Requirement %d" % i}
            for i in range(1, 46)]}
        self.claims = [{"id": "Q1"}] + [{"id": "Other%d" % i} for i in range(10)]
        self.overlay = {
            "format": gate.FORMAT, "head_sha": H,
            "compiler_axiom_receipts": [self.proof],
            "positive_test_receipts": [self.test],
            "semantic_negative_receipts": [self.negative],
            "case_decisions": [{
                "id": "case", "case_id": "C-01",
                "decision": "VERIFIED_SELECTED_SCOPE",
                "required_expected_result_sha256": sha(b"Requirement 1"),
                "proof_ids": ["p"], "positive_ids": ["t"],
                "negative_ids": ["n"], "review_id": 100}],
            "claim_decisions": [{
                "id": "claim", "claim_id": "Q1",
                "proof_ids": ["p"], "review_id": 100}],
        }
        self.scopes = {100: {"cases": {"C-01": "VERIFIED_SELECTED_SCOPE"},
                             "claims": ["Q1"]}}
        patcher = mock.patch.object(gate, "ROOT", self.repo)
        patcher.start()
        self.addCleanup(patcher.stop)

    def save(self):
        with zipfile.ZipFile(self.bundle, "w") as z:
            for name, data in self.logs.items():
                z.writestr(name, data)
        self.bundle_sha = sha(self.bundle.read_bytes())

    def check(self, overlay=None, scopes=None):
        members = gate.load_detached_bundle(self.bundle, self.bundle_sha)
        return gate.effective_acceptance(
            self.overlay if overlay is None else overlay,
            head=H, case_ledger=self.ledger, claims=self.claims,
            members=members, accepted_checks=self.checks,
            approved_review_scopes=self.scopes if scopes is None else scopes)

    def test_one_mocked_case_never_promotes_other_forty_four(self):
        r = self.check()
        self.assertEqual((r["accepted_case_count"], r["pending_case_count"],
                          r["accepted_claim_count"]), (1, 44, 1))

    def test_wrong_detached_digest_rejected(self):
        with self.assertRaises(gate.EvidenceError):
            gate.load_detached_bundle(self.bundle, "0"*64)

    def test_traversal_duplicate_and_symlink_members_rejected(self):
        for unsafe in ("../escape", "/absolute", "a\\wrong"):
            with self.subTest(unsafe=unsafe):
                with zipfile.ZipFile(self.bundle, "w") as z:
                    z.writestr(unsafe, b"payload")
                with self.assertRaises(gate.EvidenceError):
                    gate.load_detached_bundle(self.bundle, sha(self.bundle.read_bytes()))
        with zipfile.ZipFile(self.bundle, "w") as z:
            info = zipfile.ZipInfo("symlink")
            info.external_attr = (stat.S_IFLNK | 0o777) << 16
            z.writestr(info, b"target")
        with self.assertRaises(gate.EvidenceError):
            gate.load_detached_bundle(self.bundle, sha(self.bundle.read_bytes()))

    def test_archive_metadata_bombs_fail_before_extraction(self):
        with zipfile.ZipFile(self.bundle, "w") as z:
            for i in range(gate.MAX_MEMBERS + 1):
                z.writestr(f"items/{i}.log", b"x")
        with self.assertRaises(gate.EvidenceError):
            gate.load_detached_bundle(self.bundle, sha(self.bundle.read_bytes()))
        with zipfile.ZipFile(self.bundle, "w", compression=zipfile.ZIP_DEFLATED) as z:
            for i in range(gate.MAX_EXPANDED_BYTES // gate.MAX_MEMBER_BYTES + 1):
                z.writestr(f"big/{i}.log", b"z" * gate.MAX_MEMBER_BYTES)
        with self.assertRaises(gate.EvidenceError):
            gate.load_detached_bundle(self.bundle, sha(self.bundle.read_bytes()))

    def test_archive_ancestor_collision_fails(self):
        with zipfile.ZipFile(self.bundle, "w") as z:
            z.writestr("a", b"file")
            z.writestr("a/b", b"not a directory")
        with self.assertRaises(gate.EvidenceError):
            gate.load_detached_bundle(self.bundle, sha(self.bundle.read_bytes()))

    def test_wrong_head_source_header_and_namespace_rejected(self):
        for key, value in [("head_sha", "b"*40),
                           ("source_sha256", "0"*64),
                           ("elaborated_type_sha256", "0"*64),
                           ("declaration", "Other.Scope.genuine")]:
            with self.subTest(key=key):
                o = copy.deepcopy(self.overlay)
                o["compiler_axiom_receipts"][0][key] = value
                with self.assertRaises(gate.EvidenceError):
                    self.check(o)

    def test_wrong_target_axiom_list_rejected(self):
        self.logs["axiom.log"] = (
            b"Test.Scope.genuine : True\n"
            b"Other.Scope.genuine depends on axioms: []\n")
        self.save()
        o = copy.deepcopy(self.overlay)
        o["compiler_axiom_receipts"][0]["axiom_log_sha256"] = sha(self.logs["axiom.log"])
        with self.assertRaises(gate.EvidenceError):
            self.check(o)

    def test_bad_compiler_diagnostics_not_semantic(self):
        warnings = [
            b"error: unknown identifier false\nunsolved goals",
            b"error: parser error\nunsolved goals",
            b"error: maximum number of heartbeats\nunsolved goals",
            b"error: declaration uses " + bytes([96]) +
                b"sorry" + bytes([96]) + b"\nunsolved goals",
        ]
        for log in warnings:
            with self.subTest(log=log[:25]):
                self.logs["negative.log"] = log
                self.save()
                o = copy.deepcopy(self.overlay)
                o["semantic_negative_receipts"][0]["log_sha256"] = sha(log)
                with self.assertRaises(gate.EvidenceError):
                    self.check(o)

    def test_borrowed_case_and_forged_review_rejected(self):
        o = copy.deepcopy(self.overlay)
        o["case_decisions"][0]["case_id"] = "C-02"
        o["case_decisions"][0]["required_expected_result_sha256"] = sha(b"Requirement 2")
        with self.assertRaises(gate.EvidenceError):
            self.check(o)
        with self.assertRaises(gate.EvidenceError):
            self.check(scopes={})

    def test_mismatched_check_and_failed_positive_control_rejected(self):
        for key, value in [("check_run_id", 404),
                           ("positive_control", {"compiled": False})]:
            with self.subTest(key=key):
                o = copy.deepcopy(self.overlay)
                o["semantic_negative_receipts"][0][key] = value
                with self.assertRaises(gate.EvidenceError):
                    self.check(o)

    def test_duplicate_evidence_cannot_satisfy_case(self):
        o = copy.deepcopy(self.overlay)
        o["compiler_axiom_receipts"].append(copy.deepcopy(self.proof))
        with self.assertRaises(gate.EvidenceError):
            self.check(o)


if __name__ == "__main__":
    unittest.main()
