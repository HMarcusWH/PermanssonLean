"""Content mutations repair all nested hashes before archive validation."""
from copy import deepcopy
from hashlib import sha256
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import unittest
import zipfile

from c10_archive_validation import C10ArchiveError, authoritative_checker, validate_c10_archive

KIT = Path(__file__).resolve().parent
ROOT = KIT.parents[1]
ACCEPTANCE = json.loads((KIT / "acceptance-evidence.json").read_text(encoding="utf-8"))


def context(receipt):
    return {"repository": ACCEPTANCE["repository"], "pr_number": receipt["pr"],
            "head_sha": receipt["source_sha"], "base_sha": receipt["base_sha"],
            "synthetic_merge_sha": receipt["synthetic_merge_sha"]}


def encoded(value):
    return (json.dumps(value, sort_keys=True, ensure_ascii=False, indent=2) + "\n").encode()


class C10ArchiveValidationTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.receipt = next(r for r in ACCEPTANCE["receipts"] if r["anchor"] == "X1")
        cls.archive = KIT / "evidence/c10/X1-c10.zip"
        with zipfile.ZipFile(cls.archive) as zipped:
            cls.original = {name: zipped.read(name) for name in zipped.namelist()}

    def reject_rehashed(self, mutate):
        payloads = deepcopy(self.original)
        mutate(payloads)
        manifest = json.loads(payloads["evidence_manifest.json"])
        manifest["artifacts"] = {name: sha256(data).hexdigest() for name, data in payloads.items()
                                 if name != "evidence_manifest.json"}
        payloads["evidence_manifest.json"] = encoded(manifest)
        with TemporaryDirectory(prefix="c10-negative-") as temporary:
            path = Path(temporary) / "repaired-hashes.zip"
            with zipfile.ZipFile(path, "w", zipfile.ZIP_DEFLATED) as zipped:
                for name, data in payloads.items():
                    zipped.writestr(name, data)
            # A caller repairing its outer inventory can supply this valid new
            # ZIP hash. The content gate must still reject the altered claim.
            self.assertNotEqual(sha256(path.read_bytes()).digest(), sha256(self.archive.read_bytes()).digest())
            with self.assertRaises(C10ArchiveError):
                validate_c10_archive(path, context(self.receipt), ROOT)

    def mutate_json(self, name, transform):
        def mutation(payloads):
            value = json.loads(payloads[name])
            transform(value)
            payloads[name] = encoded(value)
        self.reject_rehashed(mutation)

    def test_all_seven_unchanged_publisher_archives(self):
        before = {p: sha256(p.read_bytes()).digest() for p in (KIT / "evidence/c10").glob("*.zip")}
        for receipt in ACCEPTANCE["receipts"]:
            with self.subTest(anchor=receipt["anchor"]):
                result = validate_c10_archive(KIT / f"evidence/c10/{receipt['anchor']}-c10.zip",
                                              context(receipt), ROOT)
                self.assertEqual(result["status"], "pass")
                self.assertFalse(result["compiler_rerun"])
                self.assertEqual(len(result["point_theorems"]), 8)
                self.assertEqual(len(result["mixed_theorems"]), 3)
        self.assertEqual(before, {p: sha256(p.read_bytes()).digest() for p in before})

    def test_proof_status_downgrade(self):
        self.mutate_json("evidence_manifest.json", lambda m: m["proof"].update(status="UNVERIFIED"))

    def test_missing_theorem_inventory(self):
        self.mutate_json("evidence_manifest.json", lambda m: m["proof"]["theorems"].pop())

    def test_axiom_allowlist_promotion(self):
        self.mutate_json("evidence_manifest.json", lambda m: m["proof"]["transitive_axioms_allowlist"].append("sorryAx"))

    def test_typed_realization_changed(self):
        self.mutate_json("evidence_manifest.json", lambda m: m["typed_realization"].update(scope="ARBITRARY_JSON"))

    def test_wrong_numeric_baseline(self):
        def mutate(m):
            m["baseline"]["event"][0] = "0" if m["baseline"]["event"][0] != "0" else "1"
        self.mutate_json("receipt.json", mutate)

    def test_receipt_input_mismatch(self):
        self.mutate_json("receipt.json", lambda m: m.update(input_sha256="0" * 64))

    def test_normalized_input_changed(self):
        self.mutate_json("normalized_input.json", lambda m: m.update(n=7))

    def test_raw_input_disagrees_with_normalized(self):
        self.mutate_json("input.json", lambda m: m["descriptor"].__setitem__(0, True))

    def test_coherent_valid_input_is_not_the_frozen_fixture(self):
        def mutate(payloads):
            raw = json.loads(payloads["input.json"])
            raw["descriptor"][0] = True
            with authoritative_checker(ROOT) as (_, contract):
                canonical = contract.check_input(raw).canonical()
            payloads["input.json"] = encoded(raw)
            payloads["normalized_input.json"] = encoded(canonical)
        self.reject_rehashed(mutate)

    def test_point_lean_regeneration_mismatch(self):
        self.reject_rehashed(lambda p: p.update({"C10ReifiedGolden.lean": p["C10ReifiedGolden.lean"] + b"\n-- changed\n"}))

    def test_mixed_lean_regeneration_mismatch(self):
        self.reject_rehashed(lambda p: p.update({"C10MixedGolden.lean": p["C10MixedGolden.lean"] + b"\n-- changed\n"}))

    def test_wrong_mixed_arithmetic(self):
        self.mutate_json("mixed_report.json", lambda m: m.update(baseline_event="999"))

    def test_missing_point_axiom_report(self):
        self.reject_rehashed(lambda p: p.update({"lean_check.stdout.txt": b""}))

    def test_missing_mixed_axiom_report(self):
        self.reject_rehashed(lambda p: p.update({"mixed_check.stdout.txt": b""}))

    def test_hidden_forbidden_axiom(self):
        self.reject_rehashed(lambda p: p.update({"lean_check.stdout.txt": p["lean_check.stdout.txt"].replace(b"Quot.sound", b"sorryAx", 1)}))

    def test_compiler_error_alongside_complete_axiom_reports(self):
        self.reject_rehashed(lambda p: p.update({"lean_check.stdout.txt": p["lean_check.stdout.txt"] + b"error: unsolved goals\n"}))

    def test_compiler_stderr_failure(self):
        self.reject_rehashed(lambda p: p.update({"mixed_check.stderr.txt": p["mixed_check.stderr.txt"] + b"error: process exited with code1\n"}))

    def test_unexpected_additional_theorem_report(self):
        self.reject_rehashed(lambda p: p.update({"mixed_check.stdout.txt": p["mixed_check.stdout.txt"] + b"'unlistedClaim' does not depend on any axioms\n"}))

    def test_false_exit_summary(self):
        self.reject_rehashed(lambda p: p.update({"verification_summary.txt": p["verification_summary.txt"].replace(b"exit 0", b"exit 1")}))

    def test_duplicate_json_key(self):
        self.reject_rehashed(lambda p: p.update({"receipt.json": p["receipt.json"].replace(b'"numerical_status":', b'"numerical_status":"FORGED", "numerical_status":', 1)}))


if __name__ == "__main__":
    unittest.main()
