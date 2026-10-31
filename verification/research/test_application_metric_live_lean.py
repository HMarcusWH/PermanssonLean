"""Pinned-Lean replay of checked finite metric contraction receipts.

The baseline and perturbed α/P/U inputs are reflected and their induced
matrices are the two Markov kernels on the declared finite metric space. Lean
checks the metric, every coupling and potential and both invariant laws,
proves Research's `IsW1Contraction`, assembles `ContractivePerturbation` for
the A3 bound and identifies the exact invariant-law distance. A pass proves
bounded instance theorem elaboration with an audited axiom set, not a
Polish-space moment argument, an empirical metric, provenance or release.
"""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.metric import propose_metric
from permansson_app.proof.control_emit import _fin_case
from permansson_app.proof.finite_emit import rational_expr
from permansson_app.proof.metric_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedMetric.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/metric.v1.json"


def _q(n: int, d: int) -> str:
    return f"(({n} : ℚ) / ({d} : ℚ))"


def _first(code: str, prefix: str, old: str, new: str) -> str:
    """Replace the first occurrence of `old` on the unique `prefix` line."""
    lines = code.splitlines()
    locations = [i for i, line in enumerate(lines) if line.startswith(prefix)]
    if len(locations) != 1 or old not in lines[locations[0]]:
        raise AssertionError("missing/ambiguous mutation target " + prefix)
    lines[locations[0]] = lines[locations[0]].replace(old, new, 1)
    return "\n".join(lines) + "\n"


class MetricLeanReplay(unittest.TestCase):
    _cache: tuple[str, dict, dict] | None = None

    def _positive(self):
        if MetricLeanReplay._cache is None:
            raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
            receipt = propose_metric(raw)
            code, meta = emit_source(raw, receipt)
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            exitcode, log = compile_source(code, FILENAME)
            self.assertEqual(exitcode, 0, log[-9000:])
            audited_axioms(log, meta["theorem_qualified_names"])
            MetricLeanReplay._cache = (code, meta, receipt)
        return MetricLeanReplay._cache

    def test_contraction_bound_and_transport_replay(self):
        _, meta, receipt = self._positive()
        self.assertEqual((receipt["contraction_factor"], receipt["defect"], receipt["invariant_bound"]),
                         ("1/2", "1/4", "1/2"))
        self.assertIn("invariant_metric_bound", meta["theorem_names"])

    def test_understated_contraction_factor_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def ρ ", _q(1, 2), _q(1, 3))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_nonstrict_contraction_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def ρ ", _q(1, 2), "(1 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_understated_defect_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def δ ", _q(1, 4), _q(1, 5))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_overstated_invariant_distance_rejected(self):
        code, _, _ = self._positive()
        changed = change_line(code, "def w ", _q(1, 6), _q(1, 4))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_feasible_nonoptimal_coupling_rejected(self):
        # The product coupling has the right marginals but costs more than w,
        # so it cannot certify the stated distance.
        code, _, receipt = self._positive()
        pi = [Fraction(v) for v in receipt["invariant_law"]]
        pit = [Fraction(v) for v in receipt["perturbed_invariant_law"]]
        product = _fin_case("i", [_fin_case("j", [rational_expr(a * b) for b in pit], 4) for a in pi], 4)
        line = next(l for l in code.splitlines() if l.startswith("def Cinv "))
        changed = change_line(code, "def Cinv ", line.split(":= fun i j => ", 1)[1], product)
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_non_metric_distance_table_rejected(self):
        code, _, _ = self._positive()
        changed = _first(code, "def dm ", "(2 : ℚ)", "(3 : ℚ)")
        assert_semantic_rejection(self, code, changed, "metric_checked", FILENAME)

    def test_perturbed_world_change_rejected(self):
        code, _, _ = self._positive()
        lines = code.splitlines()
        start = next(i for i, l in enumerate(lines) if l.startswith("def pert "))
        index = next(i for i in range(start, len(lines)) if lines[i].startswith("  world := "))
        old = f"(if xp = (0 : Fin 2) then {_q(1, 2)} else {_q(1, 2)})"
        lines[index] = lines[index].replace(old, f"(if xp = (0 : Fin 2) then {_q(1, 3)} else {_q(2, 3)})", 1)
        changed = "\n".join(lines) + "\n"
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
