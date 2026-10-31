"""Pinned-Lean replay of checked observe-then-act belief receipts.

The model is the reflected source's α/P/U input with its admitted actions
exactly the feasible ones, plus the literal observation kernel, prior and
terminal rewards. Lean checks the receipt's optimum, selected tree and
terminal law on unnormalized forward vectors and transfers them to Research's
chronological belief law (time-shifted embedding): every real behavioral
observation-history policy admitted on the hidden support is bounded by the
optimum, which the selected tree attains; the blind baseline is the best
admitted observation-independent sequence. A pass proves bounded instance
theorem elaboration with an audited axiom set, not unrestricted POMDP
optimality, an identified observation model, provenance or release.
"""
from __future__ import annotations

import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
APP = ROOT / "apps/permansson/application-successor"
sys.path.insert(0, str(APP / "src"))

from permansson_app.engines.belief import propose_belief
from permansson_app.engines.belief_tree import propose_belief_tree
from permansson_app.proof.belief_emit import emit_source
from application_bridge_replay import (assert_semantic_rejection, audited_axioms,
                                       change_line, compile_source)

FILENAME = "ReifiedBelief.lean"
EXAMPLES = APP / "src/permansson_app/data/examples"
RESTRICTED = APP / "tests/fixtures/belief_tree_restricted.v1.json"
DEAD_END = APP / "tests/fixtures/belief_tree_dead_end.v1.json"


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


def _replay(test: unittest.TestCase, path: Path, propose):
    raw = json.loads(path.read_text(encoding="utf-8"))
    receipt = propose(raw)
    code, meta = emit_source(raw, receipt)
    test.assertEqual(meta["lean_status"], "NOT_EXECUTED")
    exitcode, log = compile_source(code, FILENAME)
    test.assertEqual(exitcode, 0, log[-9000:])
    audited_axioms(log, meta["theorem_qualified_names"])
    return code, meta, receipt


class BeliefLeanReplay(unittest.TestCase):
    _cache: dict[str, tuple[str, dict, dict]] = {}

    def _positive(self, name: str):
        if name not in BeliefLeanReplay._cache:
            path, propose = {
                "one": (EXAMPLES / "belief.v1.json", propose_belief),
                "tree": (EXAMPLES / "belief_tree.v1.json", propose_belief_tree),
                "restricted": (RESTRICTED, propose_belief_tree),
                "dead_end": (DEAD_END, propose_belief_tree),
            }[name]
            BeliefLeanReplay._cache[name] = _replay(self, path, propose)
        return BeliefLeanReplay._cache[name]

    def test_one_step_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive("one")
        self.assertEqual(receipt["optimal_expected_terminal_reward"], "13/16")
        self.assertEqual(meta["scope"]["horizon"], 1)
        self.assertIn("value_of_observation", meta["theorem_names"])

    def test_packaged_tree_replays_with_audited_axioms(self):
        _, meta, receipt = self._positive("tree")
        self.assertEqual(receipt["optimal_expected_terminal_reward"], "55/64")
        self.assertEqual(receipt["value_of_observation_history"], "7/64")
        self.assertEqual(meta["scope"]["horizon"], 2)

    def test_restricted_horizon_three_tree_replays(self):
        _, meta, receipt = self._positive("restricted")
        self.assertEqual(receipt["optimal_expected_terminal_reward"], "121/512")
        self.assertEqual((meta["scope"]["ns"], meta["scope"]["horizon"]), (2, 3))

    def test_dead_end_action_with_equal_blind_value_replays(self):
        # `risk` at the root has no complete legal continuation and is not
        # scored; observation does not help (D = B = 2), so value_of_observation
        # is the equality case.
        _, meta, receipt = self._positive("dead_end")
        root = receipt["optimal_policy_tree"]["observations"][0]
        self.assertEqual(root["action_scores"], {"safe": "2"})
        self.assertEqual((receipt["optimal_expected_terminal_reward"],
                          receipt["best_blind_action_sequence_reward"]), ("2", "2"))
        self.assertIn("value_of_observation", meta["theorem_names"])

    def test_dead_end_action_selection_rejected(self):
        # Selecting the dead-end action at the root leaves no admitted action
        # for the second transition on the hidden support.
        code, _, _ = self._positive("dead_end")
        changed = _first(code, "def roots ", "fun o0 => ((0 : Fin 2)", "fun o0 => ((1 : Fin 2)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_overstated_optimum_rejected(self):
        code, _, _ = self._positive("tree")
        changed = change_line(code, "def D ", _q(55, 64), _q(7, 8))
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_suboptimal_admitted_action_rejected(self):
        # quiet, quiet, quiet: `wait` (3/4) is strictly better than `fix` (1/2).
        code, _, _ = self._positive("restricted")
        changed = _first(code, "def roots ", "then ((0 : Fin 2), fun _ => PUnit.unit)",
                         "then ((1 : Fin 2), fun _ => PUnit.unit)")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_inadmissible_action_of_equal_value_rejected(self):
        # quiet, silent: the hidden support is {(s0, bad)}, where only `fix` is
        # feasible; `wait`'s canonical extension row equals `fix`'s row there,
        # so only admissibility on the hidden support can reject it.
        code, _, _ = self._positive("restricted")
        changed = _first(code, "def roots ", "else ((1 : Fin 2), fun o2",
                         "else ((0 : Fin 2), fun o2")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_swapped_terminal_law_rejected(self):
        code, _, _ = self._positive("tree")
        changed = change_line(code, "def law ", f"then {_q(55, 64)} else {_q(9, 64)}",
                              f"then {_q(9, 64)} else {_q(55, 64)}")
        assert_semantic_rejection(self, code, changed, "receipt_checked", FILENAME)

    def test_overstated_blind_baseline_rejected(self):
        code, _, _ = self._positive("restricted")
        changed = change_line(code, "def B ", _q(1, 8), _q(121, 512))
        assert_semantic_rejection(self, code, changed, "blind_checked", FILENAME)

    def test_inadmissible_blind_sequence_rejected(self):
        code, _, _ = self._positive("restricted")
        changed = _first(code, "def blindSeq ", "[(1 : Fin 2)", "[(0 : Fin 2)")
        assert_semantic_rejection(self, code, changed, "blind_checked", FILENAME)

    def test_non_stochastic_observation_kernel_rejected(self):
        code, _, _ = self._positive("one")
        changed = _first(code, "def likelihood ", f"then {_q(3, 4)}", f"then {_q(1, 2)}")
        assert_semantic_rejection(self, code, changed, "likelihood_sum_one", FILENAME)

    def test_unnormalized_prior_rejected(self):
        code, _, _ = self._positive("one")
        changed = _first(code, "def priorWeight ", f"then {_q(1, 2)}", f"then {_q(1, 4)}")
        assert_semantic_rejection(self, code, changed, "prior_sum_one", FILENAME)


if __name__ == "__main__":
    unittest.main()
