"""Positive/negative contract tests. These do not certify empirical applications."""
from __future__ import annotations
import contextlib
import copy
from fractions import Fraction
import hashlib
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from referencing.exceptions import NoSuchResource
from application.examples.build_examples import HERE, NAMES, make_example
from application.validator.validate_application import (
    MAX_ARTIFACT_BYTES, MAX_JSON_BYTES, _deny_retrieval, load_json, main,
    pipeline_digest, validate_document, validator,
)


class ContractTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        files = make_example("grounded_pr_minimal")
        for name, content in files.items():
            (self.root / name).write_text(content, encoding="utf-8", newline="\n")
        self.doc = json.loads(files["application.json"])

    def seal(self):
        digest = pipeline_digest(self.doc)
        self.doc["semantic_pipeline"]["pipeline_id"] = digest
        self.doc["certificate"]["pipeline_id"] = digest

    def result(self):
        return validate_document(self.doc, self.root)

    def codes(self):
        return {e["code"] for e in self.result()["errors"]}

    def assertPass(self):
        result = self.result()
        self.assertTrue(result["contract_valid"], result["errors"])
        self.assertFalse(result["scientific_claims_verified"])

    def test_baseline_passes_without_scientific_promotion(self):
        self.assertPass()

    def test_committed_examples_match_exact_expected_errors(self):
        expected = load_json(HERE / "expectations.json")
        discovered = {p.parent.name for p in HERE.glob("*/application.json")}
        self.assertEqual(discovered, set(NAMES))
        self.assertEqual(set(expected), discovered)
        for name in NAMES:
            with self.subTest(name=name):
                path = HERE / name / "application.json"
                result = validate_document(load_json(path), path.parent)
                self.assertEqual(sorted({x["code"] for x in result["errors"]}), expected[name])
                self.assertEqual(result["contract_valid"], not expected[name])

    def test_regeneration_is_byte_reproducible(self):
        for name in NAMES:
            for filename, content in make_example(name).items():
                self.assertEqual((HERE / name / filename).read_bytes(), content.encode())

    def test_every_schema_checks_against_draft(self):
        self.assertIsNotNone(validator())

    def test_missing_required_fields_fail(self):
        for section in [None, "certificate", "semantic_pipeline", "identified_set", "regime"]:
            template = copy.deepcopy(self.doc)
            target = template if section is None else template[section]
            for key in list(target):
                with self.subTest(section=section, key=key):
                    damaged = copy.deepcopy(template)
                    del (damaged if section is None else damaged[section])[key]
                    self.assertIn("SCHEMA", {x["code"] for x in validate_document(damaged, self.root)["errors"]})

    def test_unknown_properties_fail_at_every_boundary(self):
        sections = [self.doc, self.doc["certificate"], self.doc["semantic_pipeline"],
                    self.doc["semantic_pipeline"]["bindings"], self.doc["interventions"][0],
                    self.doc["identified_set"], self.doc["regime"],
                    self.doc["provenance_graph"], self.doc["provenance_graph"]["nodes"][0]]
        for target in sections:
            target["not_a_field"] = True
            self.assertIn("SCHEMA", self.codes())
            del target["not_a_field"]

    def test_invalid_enum_and_future_version_fail(self):
        for owner, key, value in [(self.doc, "standard_version", "0.2.0"),
                                  (self.doc, "compatible_theory", "0.1.9"),
                                  (self.doc["certificate"], "direction_status", "ZERO")]:
            prior = owner[key]
            owner[key] = value
            self.assertIn("SCHEMA", self.codes())
            owner[key] = prior

    def test_strict_json_rejects_duplicates_nan_and_overflow(self):
        for content in ['{"x":1,"x":2}', '{"x":NaN}', '{"x":Infinity}', '{"x":1e9999}', '{']:
            (self.root / "bad.json").write_text(content)
            with self.assertRaises(ValueError):
                load_json(self.root / "bad.json")

    def test_json_size_limit(self):
        (self.root / "bad.json").write_bytes(b" " * (MAX_JSON_BYTES + 1))
        with self.assertRaises(ValueError):
            load_json(self.root / "bad.json")

    def test_nonfinite_direct_api_value_rejected(self):
        self.doc["regime"]["eta"] = float("nan")
        self.assertIn("JSON_VALUE", self.codes())

    def test_bad_timestamps_fail(self):
        for stamp in ["2026-09-01", "2026-09-01T00:00:00", "2026-02-30T00:00:00Z",
                      "2026-09-01T00:00:00+02:99", "2026-09-01T00:00:00-00:00"]:
            self.doc["semantic_pipeline"]["frozen_at"] = stamp
            self.assertIn("SCHEMA", self.codes(), stamp)

    def test_freeze_compares_instants_not_lexical_dates(self):
        p = self.doc["semantic_pipeline"]
        p["frozen_at"] = "2026-09-02T01:00:00+02:00"  # actually before midnight UTC
        self.seal()
        self.assertPass()
        p["frozen_at"] = "2026-09-01T23:00:00-02:00"  # actually after midnight UTC
        self.seal()
        self.assertIn("FREEZE_CHRONOLOGY", self.codes())

    def test_missing_freeze_rejected_for_registered(self):
        self.doc["semantic_pipeline"]["frozen_at"] = None
        self.seal()
        self.assertIn("FREEZE_CHRONOLOGY", self.codes())

    def test_posthoc_cannot_claim_valid_empirical_confirmation(self):
        self.doc["semantic_pipeline"]["selection_status"] = "POST_HOC_EXPLORATORY"
        self.doc["certificate"].update(selection_status="POST_HOC_EXPLORATORY", epistemic_mode="EMPIRICAL_CONFIRMATORY", provenance_status="SUPPORTED")
        self.doc["interventions"][0].update(reachable_support="SUPPORTED", causal_modularity="SUPPORTED")
        self.seal()
        self.assertEqual(self.codes(), {"POSTHOC_CONFIRMATORY"})
        self.doc["certificate"]["validity"] = "INVALID"
        self.assertPass()  # A truthful failure record is not malformed JSON.

    def test_held_out_requires_procedure_not_universal_chronology(self):
        p = self.doc["semantic_pipeline"]
        p.update(selection_status="HELD_OUT_OR_SELECTION_ADJUSTED", frozen_at="2026-09-03T00:00:00Z")
        self.doc["certificate"]["selection_status"] = p["selection_status"]
        self.seal()
        self.assertIn("SELECTION_EVIDENCE", self.codes())
        p["selection_adjustment_ref"] = "spec"
        self.seal()
        self.assertPass()

    def test_binding_and_replacement_mutations_change_digest(self):
        original = pipeline_digest(self.doc)
        for key in self.doc["semantic_pipeline"]["bindings"]:
            changed = copy.deepcopy(self.doc)
            changed["semantic_pipeline"]["bindings"][key] = "argument"
            self.assertNotEqual(pipeline_digest(changed), original, key)
        changed = copy.deepcopy(self.doc)
        changed["interventions"][0]["replacement_ref"] = "argument"
        self.assertNotEqual(pipeline_digest(changed), original)

    def test_unresealed_semantic_change_rejected(self):
        self.doc["semantic_pipeline"]["bindings"]["relevance_map"] = "argument"
        self.assertIn("PIPELINE_DIGEST", self.codes())

    def test_digest_is_object_key_order_independent(self):
        reordered = json.loads(json.dumps(self.doc, sort_keys=True))
        self.assertEqual(pipeline_digest(reordered), pipeline_digest(self.doc))

    def test_results_and_receipts_do_not_rewrite_frozen_semantics(self):
        before = pipeline_digest(self.doc)
        self.doc["semantic_pipeline"]["registration_ref"] = "argument"
        self.doc["interventions"][0]["reachable_support"] = "SUPPORTED"
        self.doc["identified_set"]["zero_effect"] = "POSSIBLE"
        self.assertEqual(before, pipeline_digest(self.doc))

    def test_artifact_tamper_rejected(self):
        (self.root / "specification.md").write_text("modified")
        self.assertIn("ARTIFACT_HASH", self.codes())
        self.doc["artifacts"][0]["sha256"] = hashlib.sha256(b"modified").hexdigest()
        self.assertIn("PIPELINE_DIGEST", self.codes())

    def test_certificate_pipeline_mismatch(self):
        self.doc["certificate"]["pipeline_id"] = "sha256:" + "f" * 64
        self.assertIn("CERTIFICATE_PIPELINE", self.codes())

    def test_missing_artifact_reference(self):
        self.doc["semantic_pipeline"]["bindings"]["descriptor"] = "missing"
        self.assertIn("MISSING_ARTIFACT_REF", self.codes())

    def test_duplicate_ids_rejected_even_when_payloads_differ(self):
        for rows in [self.doc["artifacts"], self.doc["interventions"],
                     self.doc["semantic_pipeline"]["components"], self.doc["provenance_graph"]["nodes"]]:
            extra = copy.deepcopy(rows[0])
            if "description" in extra:
                extra["description"] += " altered"
            elif "kind" in extra:
                extra["kind"] = "OTHER_PRIMITIVE"
            elif "path" in extra:
                extra["path"] = "other.md"
            else:
                extra["target_form"] = "COMPOUND"
            rows.append(extra)
            self.assertIn("DUPLICATE_ID", self.codes())
            rows.pop()

    def test_paths_reject_traversal_absolute_and_windows_ambiguity(self):
        for bad in ["../outside", "/etc/passwd", "a/../../b", "a\\b", "C:/x", "a//b", "./specification.md", "CON.txt", "a./x", "https://example.com/x"]:
            self.doc["artifacts"][0]["path"] = bad
            self.assertIn("ARTIFACT_PATH", self.codes(), bad)

    def test_case_colliding_paths_rejected(self):
        self.doc["artifacts"][1]["path"] = "SPECIFICATION.MD"
        self.assertIn("DUPLICATE_PATH", self.codes())

    def test_missing_artifact_and_directory_rejected(self):
        for name in ["absent.md", "directory"]:
            (self.root / "directory").mkdir(exist_ok=True)
            self.doc["artifacts"][0]["path"] = name
            self.assertIn("ARTIFACT_PATH", self.codes())

    def test_symlink_rejected(self):
        try:
            (self.root / "link.md").symlink_to(self.root / "specification.md")
        except OSError:
            self.skipTest("Symlink permission unavailable on this platform")
        self.doc["artifacts"][0]["path"] = "link.md"
        self.assertIn("ARTIFACT_PATH", self.codes())

    def test_artifact_size_limit(self):
        (self.root / "specification.md").write_bytes(b"x" * (MAX_ARTIFACT_BYTES + 1))
        self.assertIn("ARTIFACT_PATH", self.codes())

    def test_provenance_cycle_including_disconnected_nodes(self):
        nodes = self.doc["provenance_graph"]["nodes"]
        for key, dependency in [("cycleA", "cycleB"), ("cycleB", "cycleA")]:
            nodes.append({"id": key, "kind": "DERIVATION", "artifact_ref": "argument", "depends_on": [dependency], "description": "Disconnected cycle"})
        self.assertIn("PROVENANCE_CYCLE", self.codes())

    def test_self_support_and_missing_source(self):
        node = self.doc["provenance_graph"]["nodes"][1]
        node["depends_on"] = [node["id"]]
        self.assertIn("PROVENANCE_CYCLE", self.codes())
        node["depends_on"] = ["missing"]
        self.assertIn("MISSING_NODE_REF", self.codes())
        node["depends_on"] = []
        self.assertIn("ORPHAN_CLAIM", self.codes())

    def test_roots_cannot_claim_derived_dependencies(self):
        self.doc["provenance_graph"]["nodes"][0]["depends_on"] = ["effect"]
        self.assertIn("ROOT_DEPENDENCIES", self.codes())

    def test_certificate_cannot_cite_unrelated_root_as_claim(self):
        self.doc["certificate"]["claim_refs"] = ["primitives"]
        self.assertIn("CLAIM_REF", self.codes())

    def test_untargeted_primitives_must_be_explicit(self):
        self.doc["interventions"][0]["held_fixed_components"].remove("P")
        self.seal()
        self.assertIn("TARGET_PARTITION", self.codes())

    def test_strategic_intervention_cannot_modify_world(self):
        j = self.doc["interventions"][0]
        j["effective_target_components"].append("P")
        j["held_fixed_components"].remove("P")
        self.seal()
        self.assertIn("INTERVENTION_TYPE", self.codes())

    def test_missing_canonical_primitive_rejected(self):
        self.doc["semantic_pipeline"]["components"] = self.doc["semantic_pipeline"]["components"][:-1]
        self.seal()
        self.assertIn("CANONICAL_COMPONENTS", self.codes())

    def test_unknown_target_component(self):
        self.doc["interventions"][0]["target_components"] = ["missing"]
        self.seal()
        self.assertIn("COMPONENT_REF", self.codes())

    def test_world_intervention_is_not_strategic_pr(self):
        j = self.doc["interventions"][0]
        j.update(type="WORLD_TRANSITION", target_components=["P"], effective_target_components=["P"], held_fixed_components=["alpha", "U", "feasibility"])
        self.seal()
        self.assertIn("STRATEGIC_PROTOCOL", self.codes())

    def test_clock_and_atomicity_gates(self):
        j = self.doc["interventions"][0]
        j["schedule"] = "CLOCK_AUGMENTED"
        self.seal()
        self.assertIn("CLOCK_REQUIRED", self.codes())
        j["target_components"].append("U")
        self.seal()
        self.assertIn("ATOMIC_TARGET", self.codes())

    def test_inadmissible_intervention_cannot_support_robust_pr(self):
        self.doc["interventions"][0]["formal_admissibility"] = "INADMISSIBLE"
        self.assertIn("STRATEGIC_PROTOCOL", self.codes())

    def test_unsupported_rows_preserve_identification_failure(self):
        self.doc["certificate"]["epistemic_mode"] = "EMPIRICAL_EXPLORATORY"
        self.doc["interventions"][0].update(reachable_support="UNRESOLVED", causal_modularity="UNRESOLVED")
        self.assertIn("EMPIRICAL_IDENTIFICATION", self.codes())

    def test_quasi_regime_cannot_be_promoted_to_pr(self):
        self.doc["regime"].update(**{"class": "QUASI_REGIME", "horizon": 10, "eta": 0.1})
        self.assertIn("PR_REQUIRES_EXACT_GR", self.codes())

    def test_qsd_is_separate_from_uniform_finite_persistence(self):
        self.doc["regime"].update(**{"class": "QSD_CERTIFIED_QUASI_REGIME"})
        self.assertIn("FINITE_PERSISTENCE", self.codes())
        self.assertIn("QSD_SEPARATE_GATES", self.codes())

    def test_exact_gr_requires_occupation_and_exactness_evidence(self):
        self.doc["regime"]["exactness_basis"] = "NOT_ESTABLISHED"
        self.doc["semantic_pipeline"]["bindings"]["limiting_law"] = None
        self.seal()
        self.assertIn("EXACT_GR_EVIDENCE", self.codes())

    def test_basin_only_nondegeneracy_is_allowed(self):
        self.doc["regime"]["forward_richness"] = "BASIN_ONLY"
        self.assertPass()

    def test_pointwise_robust_pr_does_not_require_uniform_gap(self):
        self.doc["identified_set"]["uniform_gap"] = {"status": "UNRESOLVED", "lower_bound": None, "claim_refs": []}
        self.doc["certificate"]["uniform_gap_status"] = "UNRESOLVED"
        self.assertPass()

    def test_robust_pr_can_have_ambiguous_direction(self):
        self.doc["identified_set"].update(kind="SET_IDENTIFIED", direction="DIRECTION_AMBIGUOUS")
        self.doc["certificate"].update(identification_status="SET_IDENTIFIED", direction_status="DIRECTION_AMBIGUOUS")
        self.assertPass()

    def test_metric_property_need_not_have_a_signed_direction(self):
        self.doc["identified_set"]["direction"] = "NOT_APPLICABLE"
        self.doc["certificate"]["direction_status"] = "NOT_APPLICABLE"
        self.assertPass()

    def test_uniform_bound_must_be_positive(self):
        self.doc["identified_set"]["uniform_gap"]["lower_bound"] = "0"
        self.assertIn("UNIFORM_GAP", self.codes())

    def test_robust_status_rejects_empty_or_incomplete_outer_set(self):
        self.doc["identified_set"]["nonempty"] = False
        self.assertIn("ROBUST_OUTER_SET", self.codes())
        self.doc["identified_set"]["nonempty"] = True
        self.doc["identified_set"]["quantification"] = "INCOMPLETE"
        self.assertIn("ROBUST_OUTER_SET", self.codes())

    def test_zero_containing_outer_set_cannot_certify_robust_pr(self):
        self.doc["identified_set"]["zero_effect"] = "POSSIBLE"
        self.assertIn("ROBUST_OUTER_SET", self.codes())
        self.assertIn("SIGN_NONZERO", self.codes())

    def test_nonconstitution_is_protocol_scoped_not_nonsignificance(self):
        c, m = self.doc["certificate"], self.doc["identified_set"]
        c.update(substantive_pr_status="ROBUST_NONCONSTITUTIVE_UNDER_FROZEN_PROTOCOL", direction_status="NOT_APPLICABLE", uniform_gap_status="NOT_APPLICABLE")
        m.update(zero_effect="ALL_ZERO", direction="NOT_APPLICABLE", uniform_gap={"status": "NOT_APPLICABLE", "lower_bound": None, "claim_refs": []})
        self.assertPass()
        m["zero_effect"] = "POSSIBLE"
        self.assertIn("ROBUST_OUTER_SET", self.codes())
        c["scope"] = "NO_PR_ANYWHERE"
        self.assertIn("SCHEMA", self.codes())

    def test_sampling_requires_covered_joint_outer_set(self):
        self.doc["identified_set"].update(sampling_applicable=True, coverage="UNRESOLVED")
        self.doc["certificate"]["statistical_status"] = "RESOLVED_AT_DECLARED_COVERAGE"
        self.assertIn("STATISTICAL_RESOLUTION", self.codes())

    def test_schema_retrieval_is_closed(self):
        with self.assertRaises(NoSuchResource):
            _deny_retrieval("https://example.com/malicious-schema")
        with patch("socket.socket", side_effect=AssertionError("Network access forbidden")):
            self.assertPass()

    def test_cli_json_and_exit_codes(self):
        output = io.StringIO()
        with contextlib.redirect_stdout(output):
            code = main([str(self.root / "application.json"), "--json"])
        self.assertEqual(code, 0)
        self.assertTrue(json.loads(output.getvalue())["contract_valid"])
        self.assertFalse(json.loads(output.getvalue())["scientific_claims_verified"])
        for content, expected in [("{", 2), ("{}", 1)]:
            (self.root / "bad.json").write_text(content)
            with contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(main([str(self.root / "bad.json"), "--json"]), expected)
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main([str(self.root / "missing.json"), "--json"]), 2)

    def test_digest_command_never_rewrites_input(self):
        path = self.root / "application.json"
        original = path.read_bytes()
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main([str(path), "--digest"]), 0)
        self.assertEqual(original, path.read_bytes())
        (self.root / "specification.md").write_text("tampered")
        with contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(main([str(path), "--digest"]), 1)

    def test_fixture_finite_survival_argument_with_exact_rationals(self):
        self.assertGreaterEqual(Fraction(99, 100) ** 10, Fraction(9, 10))
        self.assertLess(Fraction(99, 100) ** 10, 1)

    def test_fixture_periodic_and_intervened_paths(self):
        for start in (0, 1):
            for horizon in range(1, 101):
                baseline = [(start + t) % 2 for t in range(horizon)]
                error = abs(Fraction(sum(baseline), horizon) - Fraction(1, 2))
                self.assertLessEqual(error, Fraction(1, 2 * horizon))
                intervention = [start] + [0] * (horizon - 1)
                self.assertEqual(Fraction(sum(intervention), horizon), Fraction(start, horizon))


if __name__ == "__main__":
    unittest.main()
