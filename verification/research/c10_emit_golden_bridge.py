"""Six-state-only Lean source bridge for the independently verified C10 golden.

This module does not change the generic JSON-to-Lean reifier. It appends
kernel-checked *data identity* proofs for the frozen six-state benchmark,
then transports the reified rational margins to the existing original typed
sixOriginalMargin theorem. It NEVER identifies arbitrary external games.
"""
from __future__ import annotations

from c10_emit_lean_receipt import emit_source
from c10_exact_execution import check_input
from c10_golden import six_input
from c10_verify_receipt import verify_receipt, ReceiptError

SIX_LABELS = ("full", "half", "tiny", "identity", "u-only", "b-only")


def emit_golden_bridge(receipt: dict) -> str:
    """Require the exact original six-state data and fixed index/label order."""
    verify_receipt(receipt)
    original = check_input(six_input()).canonical()
    if receipt["normalized_input"] != original:
        raise ReceiptError("not the exact frozen six-state input")
    labels = tuple(member["id"] for member in receipt["normalized_input"]["menu"])
    if labels != SIX_LABELS:
        raise ReceiptError("six-state menu indices/labels changed")
    generic = emit_source(receipt)
    extra = """
/-! # Original C10 six-state release witness

All equality checks are over the *literal reified input*, not a copied
receipt status or an assumed adapter. The six numerical Fin indices are
fixed in SIX_LABELS and in the original sixRaw definition.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-- Baseline, every candidate, the global descriptor, and the COMPLETE
frozen comparison set coincide with the original sixRaw protocol. -/
theorem reifiedGolden_data_contract :
    (∀ x y : Fin 6,
      reifiedRaw.baseline x y = sixRaw.baseline x y) ∧
    (∀ i x y : Fin 6,
      reifiedRaw.members i x y = sixRaw.members i x y) ∧
    (∀ x : Fin 6,
      reifiedRaw.descriptor x = sixRaw.descriptor x) ∧
    reifiedRaw.comparison = sixRaw.comparison := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- The receipt's exact rational margins, in its checked index order,
are the genuine original real constitutive margins on the untouched B₁. -/
theorem reifiedGolden_original_margins :
    ∀ i : Fin 6,
      (reifiedReceipt.core.reportedMargin i : ℝ) =
        sixOriginalMargin i := by
  intro i
  rcases sixOriginalMargins_exact with ⟨h0, h1, h2, h3, h4, h5⟩
  fin_cases i
  · rw [h0]; norm_num [reifiedReceipt]
  · rw [h1]; norm_num [reifiedReceipt]
  · rw [h2]; norm_num [reifiedReceipt]
  · rw [h3]; norm_num [reifiedReceipt]
  · rw [h4]; norm_num [reifiedReceipt]
  · rw [h5]; norm_num [reifiedReceipt]

/-- Selection, complete maximizer indices, and optimum are checked from
the literal complete receipt rather than inferred from a name or hash. -/
theorem reifiedGolden_selection :
    reifiedReceipt.core.selectedIndex = (0 : Fin 6) ∧
    reifiedReceipt.core.reportedOptimum = (1 : ℚ) ∧
    reifiedReceipt.core.ties = [(0 : Fin 6)] := by
  decide +kernel

/-- Every listed reified candidate is bounded by the genuine original
full-disruption margin, with the same one intervention at all starts. -/
theorem reifiedGolden_original_global_max (i : Fin 6) :
    (reifiedReceipt.core.reportedMargin i : ℝ) ≤
      sixOriginalMargin (0 : Fin 6) := by
  rw [reifiedGolden_original_margins i]
  exact sixOriginalFull_is_global_max i

#print axioms reifiedGolden_data_contract
#print axioms reifiedGolden_original_margins
#print axioms reifiedGolden_selection
#print axioms reifiedGolden_original_global_max
#print axioms PermanssonResearch.ReverseSolver.C10.six_original_baseline_exactGR
"""
    return ("import PermanssonResearch.ReverseSolver.C10SixStateBridge\n" +
            generic + "\n" + extra)
