"""Pinned-Lean replay of checked one-step risk-constrained occupancy receipts.

The controlled rows are the reflected source's fixed-action P·U rows and the
admitted actions exactly its feasible ones. Lean checks the primal flow, the
dual certificate and the reconstructed policy, proves optimality over every
admissible real randomized one-step policy within the risk cap, and
identifies the reconstructed policy's next-state law with the realized
policy model's one-step atoms. A pass proves bounded instance theorem
elaboration with an audited axiom set, not multi-stage occupancy, robust or
private-information optimality, provenance, identification or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.risk_occupancy import propose_risk
from permansson_app.proof.flow_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)
from test_application_perturbation_live_lean import _def_line

FILENAME = "ReifiedFlow.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/risk_occupancy.v1.json"
HALF = "((1 : ℚ) / (2 : ℚ))"
SPLIT = f"(if a = (0 : Fin 2) then {HALF} else {HALF})"


def _replay(test: unittest.TestCase, **changes):
    raw = dict(json.loads(EXAMPLE.read_text(encoding="utf-8")), **changes)
    receipt = propose_risk(raw)
    code, meta = emit_source(raw, receipt)
    test.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    test.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code, meta, receipt


class FlowLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if FlowLeanReplay._cache is None:
            FlowLeanReplay._cache = _replay(self)
        return FlowLeanReplay._cache

    def test_binding_cap_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(receipt["expected_terminal_reward"], "1/2")
        self.assertIn("next_state_law_actual", meta["theorem_names"])

    def test_slack_cap_with_bound_duals_replays(self):
        _, _, receipt = _replay(self, risk_cap="1")
        self.assertEqual(receipt["expected_terminal_reward"], "1")

    def test_understated_optimum_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def D ", HALF, "((1 : ℚ) / (3 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_dropped_risk_multiplier_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def lam ", "(1 : ℚ)", "(0 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_flow_over_risk_cap_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def flow ", SPLIT, "(if a = (0 : Fin 2) then (0 : ℚ) else (1 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_wrong_reconstructed_policy_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def πr ", SPLIT, "(if a = (0 : Fin 2) then (1 : ℚ) else (0 : ℚ))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_policy_world_not_the_reconstructed_policy_rejected(self):
        code, _, _ = self._positive()
        changed = _def_line(code, "policyWorld", "  alpha := ", SPLIT,
                            "(if a = (0 : Fin 2) then (1 : ℚ) else (0 : ℚ))")
        assert_semantic_rejection(self, code, changed, "policy_rows", FILENAME)


if __name__ == "__main__":
    unittest.main()
