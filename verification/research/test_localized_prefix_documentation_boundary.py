"""Regression guards for narrowly reviewable original Markdown paths.

These pure contract tests do not replace source/head binding, full Lean
compilation, axiom audits, or mandatory compiler-based semantic mutations.
"""
from __future__ import annotations

import unittest

from localized_prefix_support import (
    GuardError, REVIEWABLE_DOCUMENTATION, validated_baseline_changes,
)


class DocumentationBoundary(unittest.TestCase):
    @staticmethod
    def original():
        return {
            "PermanssonResearch.lean": ("100644", "0" * 40),
            "PermanssonLean/Regime/ConstitutiveMargin.lean": ("100644", "1" * 40),
            "lean-toolchain": ("100644", "2" * 40),
            ".github/workflows/research-lean.yml": ("100644", "3" * 40),
            "release/v0.2.0/README.md": ("100644", "4" * 40),
            "docs/RESEARCH_BUILD.md": ("100644", "5" * 40),
            "docs/README.md": ("100644", "6" * 40),
            "README.md": ("100644", "7" * 40),
            "apps/permansson/closure-successor/README.md": ("100644", "8" * 40),
            "apps/permansson/closure-successor-c11/README.md": ("100644", "9" * 40),
        }

    def test_exact_five_documentation_paths_only(self):
        self.assertEqual(REVIEWABLE_DOCUMENTATION, frozenset({
            "README.md", "docs/README.md", "docs/RESEARCH_BUILD.md",
            "apps/permansson/closure-successor/README.md",
            "apps/permansson/closure-successor-c11/README.md",
        }))
        original = self.original()
        revised = dict(original)
        for name in REVIEWABLE_DOCUMENTATION:
            revised[name] = ("100644", "a" * 40)
        self.assertEqual(validated_baseline_changes(original, revised),
                         REVIEWABLE_DOCUMENTATION)
        with self.assertRaisesRegex(GuardError, "installer requires exact"):
            validated_baseline_changes(original, revised, pristine=True)

    def test_original_math_and_dependencies_remain_immutable(self):
        original = self.original()
        for name in (
            "PermanssonLean/Regime/ConstitutiveMargin.lean",
            "lean-toolchain",
            ".github/workflows/research-lean.yml",
            "release/v0.2.0/README.md",
        ):
            changed = dict(original)
            changed[name] = ("100644", "b" * 40)
            with self.subTest(path=name), self.assertRaisesRegex(
                    GuardError, "original provider objects changed"):
                validated_baseline_changes(original, changed)

    def test_readme_executable_mode_rejected(self):
        original = self.original()
        changed = dict(original)
        changed["README.md"] = ("100755", "a" * 40)
        with self.assertRaisesRegex(GuardError, "documentation mode changed"):
            validated_baseline_changes(original, changed)

    def test_delete_historical_file_rejected(self):
        original = self.original()
        changed = dict(original)
        del changed["README.md"]
        with self.assertRaisesRegex(GuardError, "original provider path deleted"):
            validated_baseline_changes(original, changed)

    def test_unmodified_and_root_only_are_valid(self):
        original = self.original()
        self.assertEqual(validated_baseline_changes(original, original), set())
        changed = dict(original)
        changed["PermanssonResearch.lean"] = ("100644", "c" * 40)
        self.assertEqual(validated_baseline_changes(original, changed),
                         {"PermanssonResearch.lean"})


if __name__ == "__main__":
    unittest.main()
