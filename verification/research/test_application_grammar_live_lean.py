"""Pinned-Lean replay of checked admitted patch-grammar receipts bound to alpha/P/U.

Every admitted block's treated model is a reflected input proved to keep
feasibility and P and to be the baseline with exactly its declared alpha/U
patch rows. Lean decides block values, the inclusion-minimal positive blocks
and four-corner interactions and identifies them with actual path-law
probabilities. A pass proves bounded instance theorem elaboration with an
audited axiom set, not downward closure, a constitutive or PR certificate,
provenance, identification or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.grammar import propose_grammar
from permansson_app.proof.grammar_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)
from test_application_perturbation_live_lean import _def_line

FILENAME = "ReifiedGrammar.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/grammar.v1.json"


def _replay(test: unittest.TestCase, **changes):
    raw = dict(json.loads(EXAMPLE.read_text(encoding="utf-8")), **changes)
    receipt = propose_grammar(raw)
    code, meta = emit_source(raw, receipt)
    test.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    test.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code, meta, receipt


class GrammarLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if GrammarLeanReplay._cache is None:
            GrammarLeanReplay._cache = _replay(self)
        return GrammarLeanReplay._cache

    def test_packaged_exit_grammar_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(receipt["minimal_positive_blocks"], [["a"], ["u"]])
        self.assertIn("four_corner_0_0", meta["theorem_names"])

    def test_survival_variant_replays(self):
        _, _, receipt = _replay(self, value_type="survival_horizon", horizon=2)
        self.assertEqual(receipt["minimal_positive_blocks"], [])

    def test_overclaimed_minimal_set_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def minimal ", "({1, 2} : Finset (Fin 4))", "({1, 2, 3} : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_false_block_value_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def values ",
                              "(if i = (1 : Fin 4) then (if y = (0 : Fin 4) then (1 : ℚ)",
                              "(if i = (1 : Fin 4) then (if y = (0 : Fin 4) then (0 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_false_interaction_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def interactions ", "(-1 : ℚ)", "(0 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_misreported_block_components_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def blocks ", "({0, 1} : Finset (Fin 2))", "({0} : Finset (Fin 2))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_block_without_its_patch_rejected(self):
        code, _, _ = self._positive()
        # Block {a} with the baseline alpha row instead of patch `a`.
        changed = _def_line(code, "block_1", "  alpha := ",
                            "(if x = (0 : Fin 2) then (if a = (0 : Fin 2) then (0 : ℚ) else (1 : ℚ))",
                            "(if x = (0 : Fin 2) then (if a = (0 : Fin 2) then (1 : ℚ) else (0 : ℚ))")
        assert_semantic_rejection(self, code, changed, "block_1_alpha_rows", FILENAME)

    def test_block_changing_world_kernel_rejected(self):
        code, _, _ = self._positive()
        prefix = "(if s = (0 : Fin 2) then (if x = (0 : Fin 2) then (if a = (0 : Fin 2) then "
        changed = _def_line(code, "block_1", "  world := ",
                            prefix + "(if xp = (0 : Fin 2) then (1 : ℚ) else (0 : ℚ))",
                            prefix + "(if xp = (0 : Fin 2) then (0 : ℚ) else (1 : ℚ))")
        assert_semantic_rejection(self, code, changed, "block_1_held_fixed", FILENAME)


if __name__ == "__main__":
    unittest.main()
