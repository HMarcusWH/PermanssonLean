"""Source/interface guards. These do NOT certify Lean elaboration or proof truth."""
from pathlib import Path
import re
import subprocess
import unittest
from localized_prefix_support import LIBRARIES, IMPORTS, lean_code, source_firewall
from localized_prefix_gate import DECLS, MUTATIONS, mutated_source

ROOT = Path(__file__).resolve().parents[2]


class LocalizedSourceGuards(unittest.TestCase):
    def test_new_library_firewall(self):
        for rel in LIBRARIES:
            with self.subTest(path=rel):
                source_firewall((ROOT / rel).read_text(encoding="utf-8"))

    def test_direct_import_wiring_or_valid_unapplied_patch(self):
        root = ROOT / "PermanssonResearch.lean"
        if root.is_file():
            lines = lean_code(root.read_text(encoding="utf-8")).splitlines()
            for imp in IMPORTS:
                self.assertEqual(sum(line.strip() == imp for line in lines), 1)
        else:
            patch = ROOT / "integration/PermanssonResearch.lean.patch"
            text = patch.read_text(encoding="utf-8")
            for imp in IMPORTS: self.assertEqual(text.count("+" + imp + "\n"), 1)
            run = subprocess.run(["git", "apply", "--numstat", str(patch)], capture_output=True, text=True)
            self.assertEqual(run.returncode, 0, run.stderr)
            self.assertEqual(run.stdout.strip(), "4\t0\tPermanssonResearch.lean")

    def test_original_margin_definition_is_not_replaced(self):
        text = lean_code((ROOT / LIBRARIES[2]).read_text())
        self.assertIn("constitutiveMargin_perturbation_abs_le", text)
        self.assertNotRegex(text, r"\b(?:def|theorem|abbrev)\s+constitutiveMargin\b")
        self.assertIn("finitePathExpectation_eq_baselineProperty", text)
        self.assertIn("finitePathExpectation_eq_intervenedProperty", text)

    def test_pair_matches_components_and_targets_without_shared_P_constraint(self):
        text = lean_code((ROOT / LIBRARIES[2]).read_text())
        self.assertIn("PrimitiveModelPair M F J", text)
        self.assertNotIn("StrategicApproximationPair", text)
        self.assertNotIn("approx_world_eq", text)
        fixture = lean_code((ROOT / LIBRARIES[3]).read_text())
        self.assertIn("component_eq := rfl", fixture)
        self.assertIn("target_eq := rfl", fixture)

    def test_initial_error_is_wired_into_actual_original_margin_output(self):
        text = lean_code((ROOT / LIBRARIES[2]).read_text())
        for name in ("approxBaseInitial", "approxTreatedInitial", "initialBase_error",
                     "initialTreated_error", "initialBaseError +", "initialTreatedError +"):
            self.assertIn(name, text)
        self.assertEqual(text.count("have hb := finitePathExpectation_abs_le_goodVisits_initial"), 2)
        self.assertIn("f.expected T (mixedFinitePrefixLaw", text)

    def test_true_baseline_and_treatment_have_separate_visit_laws(self):
        text = lean_code((ROOT / LIBRARIES[2]).read_text())
        self.assertIn("finitePrefixLaw M.inducedKernel y n (baseGood n)ᶜ", text)
        self.assertIn("finitePrefixLaw J.intervention.apply.inducedKernel y n (treatedGood n)ᶜ", text)
        self.assertIn("∀ y ∈ B₁.states", text)

    def test_majorant_has_classical_instance_and_explicit_upper_bound(self):
        text = lean_code((ROOT / LIBRARIES[0]).read_text())
        definition = text.split("noncomputable def goodHistoryMajorant", 1)[1].split("lemma", 1)[0]
        self.assertIn("classical", definition)
        self.assertIn("if h ∈ E then eta else 1", definition)
        self.assertIn("lemma goodHistoryMajorant_le_one", text)

    def test_correct_set_image_equality_direction(self):
        text = lean_code((ROOT / LIBRARIES[3]).read_text())
        self.assertIn("(reportedEffect_four_fifths y).trans hx'.symm", text)
        self.assertNotIn("hx'.trans (reportedEffect_four_fifths y).symm", text)

    def test_positive_corollaries_use_correct_abs_arms(self):
        text = lean_code((ROOT / LIBRARIES[2]).read_text())
        first, second = text.split("theorem trueMargin_pos_of_reported", 1)[1].split(
            "theorem reportedMargin_pos_of_true", 1)
        self.assertIn("(abs_le.mp habs).2", first)
        self.assertIn("(abs_le.mp habs).1", second)

    def test_mutants_are_unique_edits_to_actual_positive_fixture(self):
        source = (ROOT / LIBRARIES[3]).read_text()
        for name in MUTATIONS:
            mutant = mutated_source(source, name)
            self.assertNotEqual(source, mutant)
            self.assertEqual(mutant.count("import "), source.count("import "))
            source_firewall(mutant)
        self.assertIn("mixedFinitePrefixLaw", mutated_source(source, "omit_zero_horizon_initial_error"))

    def test_no_automatic_GR_or_empirical_promotion(self):
        text = lean_code((ROOT / LIBRARIES[2]).read_text())
        for forbidden in ("IsExactGeneratedRegime", "IsUniformGeneralizedPermanssonRegimeRelative",
                          "empiricallyIdentified"):
            self.assertNotIn(forbidden, text)

    def test_compiler_gate_is_installed_and_discovered(self):
        """Historical compiler remains exact; active30 uses authenticated v3.

        A changed installed source may NOT borrow the original PR80 proof:
        the historical test is checked at its real introducer Git object.
        The current installed test must match the exact staged successor.
        Neither path may be skipped or relabelled as mathematical acceptance.
        """
        from pr113_a2_successor_identity_v2 import (
            HISTORICAL_A2_INTRODUCER, LATE_A2_TEST_ORIGINAL_BLOB,
            LATE_A2_TEST_PROPOSED_BLOB,
        )
        from pr113_workflow_profile_v2 import audited_source_phase

        rel = "verification/research/test_localized_prefix_compiler.py"
        original_oid = subprocess.check_output(
            ["git", "rev-parse", HISTORICAL_A2_INTRODUCER + ":" + rel],
            cwd=ROOT, stderr=subprocess.DEVNULL, timeout=20,
            text=True,
        ).strip()
        self.assertEqual(original_oid, LATE_A2_TEST_ORIGINAL_BLOB)
        original = subprocess.check_output(
            ["git", "show", HISTORICAL_A2_INTRODUCER + ":" + rel],
            cwd=ROOT, stderr=subprocess.DEVNULL, timeout=20,
        )
        self.assertIn(
            b'report = verify(ROOT, out, mode="focused")', original)
        self.assertNotIn(b"skipTest", original)

        checked = subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT,
            stderr=subprocess.DEVNULL, timeout=20, text=True,
        ).strip()
        phase, profile = audited_source_phase(ROOT, checked)
        self.assertIn(phase, {"staged", "active"})
        self.assertEqual(profile["historical_original_workflow_count"], 25)
        self.assertEqual(profile["current_reviewed_workflow_count"], 30)

        installed = (ROOT / rel).read_bytes()
        if phase == "staged":
            # Current engineering discovery freshly replays the unchanged
            # executor at original A2; it does not compare new H to old H.
            import hashlib
            from pr113_a2_successor_identity import INHERITED_A2_VERIFIERS
            actual = hashlib.sha1(
                b"blob " + str(len(installed)).encode() + b"\0" + installed
            ).hexdigest()
            self.assertEqual(actual, INHERITED_A2_VERIFIERS[rel])
            self.assertEqual(actual, subprocess.check_output(
                ["git", "rev-parse", "HEAD:" + rel], cwd=ROOT,
                text=True, timeout=20).strip())
            self.assertIn(b"from pr113_historical_a2_replay_v1 import verify", installed)
            self.assertIn(b'HISTORICAL_A2_AND_CURRENT_SOURCE', installed)
            current = (ROOT / "verification/research/test_pr113_a2_successor_compiler.py").read_text()
            self.assertIn("selected = select_compiler(ROOT)", current)
            self.assertIn('record = compiler.verify(ROOT, folder, mode="focused")', current)
            self.assertNotIn("skipTest", current)
            self.assertNotIn("@unittest.skip", current)
        else:
            staged = (
                "docs/operations/pr113_required_gate_replacement_unapproved/"
                "test_localized_prefix_compiler.py"
            )
            self.assertEqual(subprocess.check_output(
                ["git", "rev-parse", "HEAD:" + staged],
                cwd=ROOT, stderr=subprocess.DEVNULL, timeout=20,
                text=True,
            ).strip(), LATE_A2_TEST_PROPOSED_BLOB)
            self.assertEqual(installed, (ROOT / staged).read_bytes())
            self.assertIn(b"check_stored(candidate, producer_id, reviewer_id)",
                          installed)
            self.assertIn(b"strict_json_object(", installed)
            self.assertIn(b"PERMANSSON_HISTORICAL_REQUIRED_RECEIPT", installed)
            self.assertIn(
                b"PR113_HISTORICAL_SOURCE_REVERIFIED_FOR_AUTHENTIC_DESCENDANT",
                installed)
            self.assertNotIn(
                b'report = verify(ROOT, out, mode="focused")', installed)
        self.assertNotIn(b"skipTest", installed)
        self.assertNotIn(b"@unittest.skip", installed)
        gate = (ROOT / "verification/research/localized_prefix_gate.py").read_text()
        self.assertNotIn("unittest discover", gate)
        for rel in LIBRARIES:
            self.assertTrue((ROOT / rel).is_file())

    def test_audit_declarations_are_unique_and_located(self):
        self.assertEqual(len(DECLS), len(set(DECLS)))
        source = "\n".join(lean_code((ROOT / rel).read_text()) for rel in LIBRARIES)
        discovered = set(re.findall(r"\b(?:def|lemma|theorem|structure|instance)\s+([A-Za-z_][A-Za-z0-9_']*)", source))
        self.assertEqual(discovered, {decl.rsplit(".", 1)[-1] for decl in DECLS})
        for decl in DECLS:
            short = decl.rsplit(".", 1)[-1]
            self.assertRegex(source, rf"\b(?:def|lemma|theorem|structure|instance)\s+{re.escape(short)}\b")

    def test_scope_counts_are_data_not_unverified_compiler_claims(self):
        import json
        matrix = json.loads((ROOT / "research/paper_closures/post_merge_79/A2_P02_ACCEPTANCE_MATRIX.json").read_text())
        self.assertEqual(matrix["formal_status"], "SOURCE_REVIEWED_COMPILER_PENDING")
        self.assertFalse(matrix["accepted"])
        self.assertEqual(len({row["id"] for row in matrix["requirements"]}), len(matrix["requirements"]))


if __name__ == "__main__":
    unittest.main()
