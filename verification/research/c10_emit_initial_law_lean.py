"""Reify the genuine original six-state 1/2-u + 1/2-a0 initial-law query.

Both initial weights and all mixed numeric claims are computed and checked
independently before emission. The Lean theorem uses the actual checked
sixStateMatrix and C10 rational weighted evaluator, not Python axioms.
"""
from __future__ import annotations

from c10_exact_execution import check_input
from c10_golden import six_input
from c10_eval_initial_law import LAW_FORMAT, InitialLawError
from c10_verify_initial_law import verify_initial_report

MIXED_LAW = {
    "format": LAW_FORMAT,
    "weights": ["0", "1/2", "1/2", "0", "0", "0"],
}
MIXED_PROOFS = (
    "mixedGolden_exact",
    "PermanssonResearch.ReverseSolver.C10.rationalInitialProbability_singleton",
    "PermanssonResearch.ReverseSolver.C10.checked_rationalMixedEventValue_eq_actual_path",
)


def emit_mixed_golden(receipt: dict, report: dict) -> str:
    if receipt["normalized_input"] != check_input(six_input()).canonical():
        raise InitialLawError("not the exact frozen original six-state numerical input")
    verify_initial_report(receipt, MIXED_LAW, report)
    expected = {
        "full": "0", "half": "1/4", "tiny": "999/2000",
        "identity": "1", "u-only": "1/2", "b-only": "1",
    }
    if report["baseline_event"] != "1" or {
        x["id"]: x["event"] for x in report["members"]
    } != expected:
        raise InitialLawError("mixed law does not match the frozen original witness")

    return """import PermanssonResearch.ReverseSolver.C10RationalInitialMixture
import PermanssonResearch.ReverseSolver.ExactSixStateC10Execution
import Mathlib.Tactic

/-! The unmodified original six-state menu and two comparison starts,
initialized with exactly 1/2 mass each. Mixing changes neither the
original B₁ nor the fixed-menu maximin optimizer. -/
open PermanssonResearch.ReverseSolver.C10
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

def mixedGoldenWeights (x : Fin 6) : ℚ :=
  if x = 1 then 1/2 else if x = 2 then 1/2 else 0

def mixedGoldenLaw : RationalInitialLaw 6 :=
  (validateInitialLaw mixedGoldenWeights).get (by decide +kernel)

/-- Exact baseline, full, half, tiny, identity, U-only, B-only
mixed event values from C10's checked rational class receipt. -/
theorem mixedGolden_exact :
    rationalMixedEventValue sixReference.baseline
      sixRaw.descriptor mixedGoldenLaw = 1 ∧
    rationalMixedEventValue (sixReference.members (0 : Fin 6))
      sixRaw.descriptor mixedGoldenLaw = 0 ∧
    rationalMixedEventValue (sixReference.members (1 : Fin 6))
      sixRaw.descriptor mixedGoldenLaw = (1/4 : ℚ) ∧
    rationalMixedEventValue (sixReference.members (2 : Fin 6))
      sixRaw.descriptor mixedGoldenLaw = (999/2000 : ℚ) ∧
    rationalMixedEventValue (sixReference.members (3 : Fin 6))
      sixRaw.descriptor mixedGoldenLaw = 1 ∧
    rationalMixedEventValue (sixReference.members (4 : Fin 6))
      sixRaw.descriptor mixedGoldenLaw = (1/2 : ℚ) ∧
    rationalMixedEventValue (sixReference.members (5 : Fin 6))
      sixRaw.descriptor mixedGoldenLaw = 1 := by
  decide +kernel

#print axioms mixedGolden_exact
#print axioms PermanssonResearch.ReverseSolver.C10.rationalInitialProbability_singleton
#print axioms PermanssonResearch.ReverseSolver.C10.checked_rationalMixedEventValue_eq_actual_path
"""


if __name__ == "__main__":
    from pathlib import Path
    import json
    import sys
    from c10_eval_initial_law import eval_initial_law
    from c10_golden import create_golden
    if len(sys.argv) != 2:
        raise SystemExit("usage: c10_emit_initial_law_lean.py output-file.lean")
    import tempfile
    with tempfile.TemporaryDirectory() as d:
        r = create_golden(d)
        report = eval_initial_law(r, MIXED_LAW)
        Path(sys.argv[1]).write_text(emit_mixed_golden(r, report), encoding="utf-8")
