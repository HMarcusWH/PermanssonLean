"""Pinned-Lean replay of checked finite two-player protocol receipts.

The canonical tables become literal rational tables; Lean checks every row
is stochastic and that the declared baseline, closed-loop and open-loop joint
matrices are the product-protocol rows, then states that Research's assembled
`FiniteProduct.Generator` models have exactly those rows and the binary
path-law transport. A pass proves bounded instance theorem elaboration with
an audited axiom set, not asymmetric types, mediated actions, empirical game
identification, provenance or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.multiagent import propose_multiagent
from permansson_app.proof.multiagent_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedMultiAgent.lean"
EXAMPLE = APP / "src/permansson_app/data/examples/multiagent.v1.json"


def _q(n: int, d: int) -> str:
    return f"(({n} : ℚ) / ({d} : ℚ))"


def _in_def(code: str, name: str, prefix: str, old: str, new: str) -> str:
    """Replace the first `old` on the first `prefix` line after `def <name> `."""
    lines = code.splitlines()
    start = next(i for i, line in enumerate(lines) if line.startswith(f"def {name} "))
    index = next(i for i in range(start, len(lines)) if lines[i].startswith(prefix))
    if old not in lines[index]:
        raise AssertionError("missing mutation fragment: " + old)
    lines[index] = lines[index].replace(old, new, 1)
    return "\n".join(lines) + "\n"


class MultiAgentLeanReplay(unittest.TestCase):
    _cache: str | None = None

    def _code(self) -> str:
        if MultiAgentLeanReplay._cache is None:
            raw = json.loads(EXAMPLE.read_text(encoding="utf-8"))
            code, meta = emit_source(raw, propose_multiagent(raw))
            self.assertEqual(meta["lean_status"], "NOT_EXECUTED")
            exitcode, log = compile_source(code, FILENAME)
            self.assertEqual(exitcode, 0, log[-9000:])
            audited_axioms(log, meta["theorem_qualified_names"])
            MultiAgentLeanReplay._cache = code
        return MultiAgentLeanReplay._cache

    def test_protocol_replays_with_audited_axioms(self):
        self.assertIn("theorem protocol_kernels", self._code())

    def test_false_baseline_row_rejected(self):
        code = self._code()
        changed = _in_def(code, "K", "def K ", _q(27, 64), _q(7, 16))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_open_loop_value_as_closed_loop_rejected(self):
        code = self._code()
        changed = _in_def(code, "Kc", "def Kc ", _q(117, 256), _q(45, 128))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_non_stochastic_action_row_rejected(self):
        code = self._code()
        changed = _in_def(code, "p0", "  ⟨fun y a", _q(3, 4), _q(1, 2))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_changed_replacement_mechanism_rejected(self):
        code = self._code()
        changed = _in_def(code, "r", "  ⟨fun y a", "(1 : ℚ) else (0 : ℚ)", "(0 : ℚ) else (1 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_changed_anchor_profile_rejected(self):
        code = self._code()
        changed = _in_def(code, "anchor1", "  ⟨fun y a", "(0 : ℚ) else (1 : ℚ)", "(1 : ℚ) else (0 : ℚ)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_wrong_treated_player_rejected(self):
        code = self._code()
        changed = change_line(code, "def i ", ":= 0", ":= 1")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_changed_world_kernel_rejected(self):
        code = self._code()
        changed = _in_def(code, "c", "   fun y a x =>", f"then {_q(7, 8)} else {_q(1, 8)}",
                          f"then {_q(3, 4)} else {_q(1, 4)}")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)


if __name__ == "__main__":
    unittest.main()
