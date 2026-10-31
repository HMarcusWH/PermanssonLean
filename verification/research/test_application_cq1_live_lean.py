"""Pinned-Lean replay of checked CQ-1 finite constitutive certificates.

The baseline and treated α/P/U inputs are reflected; the treated one is
proved to keep feasibility and P (and U for an α-only intervention). Their
induced matrices drive Research's realized typed model and typed admissible
strategic intervention. Lean checks region-wide killed survival, the
comparison effects and the margin, constructs `FiniteConstitutiveCertificate`
and identifies the margin with the original constitutive margin. A pass
proves bounded instance theorem elaboration with an audited axiom set, not
Exact GR/PR, QSD, error-budget transport, provenance or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.cq1 import propose_cq1
from permansson_app.proof.cq1_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)
from test_application_perturbation_live_lean import _def_line

FILENAME = "ReifiedCQ1.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/cq1.v1.json"


def _q(n: int, d: int) -> str:
    return f"(({n} : ℚ) / ({d} : ℚ))"


def _replay(test: unittest.TestCase, **changes):
    raw = dict(json.loads(EXAMPLE.read_text(encoding="utf-8")), **changes)
    receipt = propose_cq1(raw)
    code, meta = emit_source(raw, receipt)
    test.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    test.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code, meta, receipt


class CQ1LeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if CQ1LeanReplay._cache is None:
            CQ1LeanReplay._cache = _replay(self)
        return CQ1LeanReplay._cache

    def test_certificate_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive()
        self.assertEqual(receipt["uniform_margin"], "8/25")
        self.assertIn("finite_constitutive_certificate", meta["theorem_names"])

    def test_horizon_three_certificate_replays(self):
        _, _, receipt = _replay(self, horizon=3, eta="3/5")
        self.assertEqual(receipt["certificate_status"], "FINITE_CONSTITUTIVE_CERTIFICATE")

    def test_overstated_margin_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def κ ", _q(8, 25), _q(39, 100))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_unattained_margin_rejected(self):
        # A valid lower bound that no comparison state attains is not the margin.
        code, _, _ = self._positive()
        changed = change_line(code, "def κ ", _q(8, 25), _q(1, 5))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_persistence_budget_too_small_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def η ", _q(2, 5), _q(1, 4))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_region_only_leaking_state_rejected(self):
        # The comparison states are unchanged; the added region state (calm, bad)
        # survives only with 1/4, so region-wide persistence fails.
        code, _, _ = self._positive()
        changed = change_line(code, "def R ", "{0, 2}", "{0, 1, 2}")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_comparison_outside_basin_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def basin ", "{0, 2}", "{0}")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_treated_world_kernel_change_rejected(self):
        code, _, _ = self._positive()
        head = "(if s = (0 : Fin 2) then (if x = (0 : Fin 2) then (if a = (0 : Fin 2) then "
        changed = _def_line(code, "treated", "  world := ",
                            head + f"(if xp = (0 : Fin 2) then {_q(9, 10)} else {_q(1, 10)})",
                            head + f"(if xp = (0 : Fin 2) then {_q(4, 5)} else {_q(1, 5)})")
        assert_semantic_rejection(self, code, changed, "treated_held_fixed", FILENAME)


if __name__ == "__main__":
    unittest.main()
