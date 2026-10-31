"""Pinned-Lean replay of checked CQ-1 certificate transport receipts.

The certified pair and the approximate pair are reflected `FiniteWorldInput`s
that keep the certified baseline's feasible actions and P; the CQ-1 values
and the row budgets are literal rationals. Lean decides the CQ-1 checks, the
budgets and the remaining-margin condition, and states the approximate
pair's transported finite constitutive certificate through Research's
`transportFiniteConstitutiveCertificate`. A pass proves bounded instance
theorem elaboration with an audited axiom set, not Exact GR/PR, empirical
error estimates, provenance or release.
"""
from __future__ import annotations

import copy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.cq1_transport import propose_cq1_transport
from permansson_app.proof.cq1_transport_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedCQ1Transport.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/cq1_transport.v1.json"


def _q(n: int, d: int) -> str:
    return f"(({n} : ℚ) / ({d} : ℚ))"


def _replay(case, raw):
    code, meta = emit_source(raw, propose_cq1_transport(raw))
    case.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    case.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code


class CQ1TransportLeanReplay(unittest.TestCase):
    _cache: str | None = None

    def _code(self) -> str:
        if CQ1TransportLeanReplay._cache is None:
            raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
            CQ1TransportLeanReplay._cache = _replay(self, raw)
        return CQ1TransportLeanReplay._cache

    def test_example_replays_with_audited_axioms(self):
        self.assertIn("theorem transported_certificate", self._code())

    def test_zero_budget_pair_replays(self):
        raw = copy.deepcopy(json.loads(EXAMPLE.read_text(encoding="utf-8")))
        raw["approximate"] = {"baseline": copy.deepcopy(raw["cq1"]["baseline"]),
                              "treated": copy.deepcopy(raw["cq1"]["intervention"]["treated"])}
        self.assertIn("def δ₀ : ℚ := (0 : ℚ)", _replay(self, raw))

    def test_understated_budget_rejected(self):
        code = self._code()
        changed = change_line(code, "def δ₀ ", _q(1, 50), _q(1, 100))
        assert_semantic_rejection(self, code, changed, "transport_checked", FILENAME)

    def test_budget_exceeding_the_margin_rejected(self):
        code = self._code()
        changed = change_line(code, "def δJ ", _q(1, 50), _q(1, 4))
        assert_semantic_rejection(self, code, changed, "transport_checked", FILENAME)

    def test_wrong_approximate_baseline_rejected(self):
        code = self._code()
        changed = change_line(code, "def A₀ ", "inducedMatrix approxBase", "inducedMatrix approxTreated")
        assert_semantic_rejection(self, code, changed, "transport_checked", FILENAME)

    def test_overstated_certified_margin_rejected(self):
        code = self._code()
        changed = change_line(code, "def κ ", _q(8, 25), _q(1, 2))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_understated_persistence_error_rejected(self):
        # Minimum region survival is 16/25, so the gate fails for eta = 1/5.
        code = self._code()
        changed = change_line(code, "def η ", _q(2, 5), _q(1, 5))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
