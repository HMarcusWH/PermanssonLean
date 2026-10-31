"""Pinned-Lean replay of checked one-step risk-cap infeasibility receipts.

The model is a reflected `FiniteWorldInput` whose fixed-action P·U rows and
exactly-feasible admitted actions are the flow bridge's; the per-state risk
floors are literal rationals. Lean decides the floor checks and states that
their initial-law total is the least risk mass of every admissible real
randomized one-step policy, attained, and that every such policy exceeds the
cap. A pass proves bounded instance theorem elaboration with an audited axiom
set, not multi-stage occupancy, empirical identification, provenance or
release.
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

from permansson_app.engines.risk_infeasibility import propose_risk_infeasibility
from permansson_app.proof.risk_infeasibility_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedRiskInfeasibility.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/risk_infeasibility.v1.json"


def _q(n: int, d: int) -> str:
    return f"(({n} : ℚ) / ({d} : ℚ))"


def _replay(case, raw):
    code, meta = emit_source(raw, propose_risk_infeasibility(raw))
    case.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    case.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code


class RiskInfeasibilityLeanReplay(unittest.TestCase):
    _cache: str | None = None

    def _code(self) -> str:
        if RiskInfeasibilityLeanReplay._cache is None:
            raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
            RiskInfeasibilityLeanReplay._cache = _replay(self, raw)
        return RiskInfeasibilityLeanReplay._cache

    def test_example_replays_with_audited_axioms(self):
        self.assertIn("theorem cap_infeasible", self._code())

    def test_zero_mass_state_instance_replays(self):
        raw = copy.deepcopy(json.loads(EXAMPLE.read_text(encoding="utf-8")))
        raw["initial_law"] = [{"mass": "0", "state": ["s", "safe"]}, {"mass": "1", "state": ["s", "danger"]}]
        raw["risk_cap"] = "1/2"
        self.assertIn("theorem min_risk", _replay(self, raw))

    def test_cap_at_the_floor_total_rejected(self):
        code = self._code()
        changed = change_line(code, "def cap ", _q(1, 4), _q(7, 16))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_floor_above_an_admitted_action_rejected(self):
        code = self._code()
        changed = change_line(code, "def v ", f"then {_q(1, 4)} else", f"then {_q(1, 2)} else")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_unattained_floor_rejected(self):
        code = self._code()
        changed = change_line(code, "def v ", "else (1 : ℚ))", f"else {_q(1, 2)})")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_changed_initial_law_rejected(self):
        code = self._code()
        changed = change_line(code, "def μ ", f"then {_q(3, 4)} else {_q(1, 4)}", "then (1 : ℚ) else (0 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_changed_risk_set_rejected(self):
        code = self._code()
        changed = change_line(code, "def risk ", "({1} : Finset (Fin 2))", "({0} : Finset (Fin 2))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
