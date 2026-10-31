"""Pinned-Lean replay of checked adaptive admitted-block control receipts.

The baseline and every admitted block are reflected `FiniteWorldInput`s with
the grammar bridge's per-block theorems; the blocks are the controls of
`blockSystem`, the region flag is `regionMonitor`, and the reported Bellman
table is literal. Lean decides the table checks and states, per start state,
that no full-history behavioral block controller exceeds the adaptive value
and one attains it. A pass proves bounded instance theorem elaboration with
an audited axiom set, not frozen-block comparisons, empirical identification,
provenance or release.
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

from permansson_app.engines.adaptive import propose_adaptive
from permansson_app.proof.adaptive_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedAdaptive.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/adaptive.v1.json"


def _q(n: int, d: int) -> str:
    return f"(({n} : ℚ) / ({d} : ℚ))"


def _first(code: str, prefix: str, old: str, new: str) -> str:
    """Replace the first `old` on the unique line starting with `prefix`."""
    lines = code.splitlines()
    index = [i for i, line in enumerate(lines) if line.startswith(prefix)]
    if len(index) != 1 or old not in lines[index[0]]:
        raise AssertionError("missing mutation target: " + old)
    lines[index[0]] = lines[index[0]].replace(old, new, 1)
    return "\n".join(lines) + "\n"


def _replay(case, raw):
    code, meta = emit_source(raw, propose_adaptive(raw))
    case.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    case.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code


class AdaptiveLeanReplay(unittest.TestCase):
    _cache: str | None = None

    def _code(self) -> str:
        if AdaptiveLeanReplay._cache is None:
            raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
            AdaptiveLeanReplay._cache = _replay(self, raw)
        return AdaptiveLeanReplay._cache

    def test_example_replays_with_audited_axioms(self):
        self.assertIn("theorem adaptive_optimal_2", self._code())

    def test_exit_objective_with_single_block_replays(self):
        raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
        raw = copy.deepcopy(raw)
        raw["grammar"].update(value_type="exit_by_horizon", admitted_blocks=[[]], horizon=3)
        self.assertIn("regionMonitor region false", _replay(self, raw))

    def test_overstated_adaptive_value_rejected(self):
        code = self._code()
        changed = _first(code, "def table ", _q(9, 16), _q(5, 8))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_no_block_helps_claim_rejected(self):
        # One step from s0 the best block survives with 3/4; the baseline gives 1/2.
        code = self._code()
        changed = _first(code, "def table ", _q(3, 4), _q(1, 2))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_dropped_block_rejected(self):
        code = self._code()
        changed = change_line(code, "def members ", "then inducedMatrix block_1 else",
                              "then inducedMatrix block_0 else")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_shrunk_region_rejected(self):
        code = self._code()
        changed = change_line(code, "def region ", "({0, 2} : Finset (Fin 4))", "({0} : Finset (Fin 4))")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_exit_objective_for_survival_table_rejected(self):
        code = self._code()
        changed = change_line(code, "def M ", "regionMonitor region true", "regionMonitor region false")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_longer_horizon_rejected(self):
        code = self._code()
        changed = change_line(code, "def horizon ", ":= 2", ":= 3")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
