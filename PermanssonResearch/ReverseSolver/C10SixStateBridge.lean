import PermanssonResearch.ReverseSolver.C10ReceiptSemantics
import PermanssonResearch.ReverseSolver.ExactSixStateC10Execution
import PermanssonResearch.ReverseSolver.ExactSixStateBOnly
import PermanssonResearch.ReverseSolver.C10ReferenceReceipt
import PermanssonResearch.MultipleLimit.ExactSixStateObservedGR
import Mathlib.Tactic

/-!
# C10 — original six-state exact values in the genuine typed margin

This module closes the six-state release interface without replacing the
proper original comparison basin, descriptor, intervention grammar, or
original Exact-GR certificate with a lookalike numeric surrogate. The
already kernel-reduced rational fractions are transported to the actual
unmodified original constitutiveMargin.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false
open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteStrategicRealization
open FrozenConstitutiveMenu
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
open PermanssonResearch.MultipleLimit.ExactSixState
open PermanssonResearch.MultipleLimit.ExactSixStateCanonical
open PermanssonResearch.MultipleLimit.ExactSixStateTyped
open PermanssonResearch.MultipleLimit.ExactSixStateConstitution
open PermanssonResearch.MultipleLimit.ExactSixStateObservedGR

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- The original relative constitutive margin of each of the six
genuinely admissible, separately typed D0 alpha-only menu members. -/
def sixOriginalMargin (i : Fin 6) : ℝ :=
  menuConstitutiveMargin typedModel observedSpec
    (researchActionFamily sixStateMatrix) comparison
    (realizedNumericMenu sixRaw sixChecked) i

/-- Original real values equal their computed rational values, requiring
actual agreement of the frozen global descriptor and the complete B₁. -/
theorem sixOriginalMargin_eq_numeric (i : Fin 6) :
    sixOriginalMargin i =
      (numericalMargin sixRaw sixChecked sixReference i : ℝ) := by
  exact realized_numeric_menu_margin sixRaw sixChecked sixReference
    sixReference_valid observedSpec comparison
    sixDescriptor_frozen sixComparison_complete i

/-- Every original typed margin is established numerically and exactly,
not merely as a Python fixture or support-graph yes/no statement. -/
theorem sixOriginalMargins_exact :
    sixOriginalMargin (0 : Fin 6) = 1 ∧
    sixOriginalMargin (1 : Fin 6) = (1/2 : ℝ) ∧
    sixOriginalMargin (2 : Fin 6) = (1/1000 : ℝ) ∧
    sixOriginalMargin (3 : Fin 6) = 0 ∧
    sixOriginalMargin (4 : Fin 6) = 0 ∧
    sixOriginalMargin (5 : Fin 6) = 0 := by
  rcases sixMargins_exact with ⟨h0, h1, h2, h3, h4, h5⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [sixOriginalMargin_eq_numeric, h0]
    norm_num
  · rw [sixOriginalMargin_eq_numeric, h1]
    norm_num
  · rw [sixOriginalMargin_eq_numeric, h2]
    norm_num
  · rw [sixOriginalMargin_eq_numeric, h3]
    norm_num
  · rw [sixOriginalMargin_eq_numeric, h4]
    norm_num
  · rw [sixOriginalMargin_eq_numeric, h5]
    norm_num

/-- The selected full intervention genuinely maximizes the original
constitutive margin across ALL six listed typed interventions. -/
theorem sixOriginalFull_is_global_max (i : Fin 6) :
    sixOriginalMargin i ≤ sixOriginalMargin (0 : Fin 6) := by
  have h := realized_numeric_menu_selected_dominates
    sixRaw sixChecked sixReference sixReference_valid
    observedSpec comparison sixDescriptor_frozen sixComparison_complete i
  have hbest : selectBest sixRaw sixChecked sixReference =
      (0 : Fin 6) := sixBest_exact.2
  rw [hbest] at h
  exact h

/-- The complete numerical reference construction agrees with the
checked six-state certificate at EVERY finite state, by the universal
uniqueness theorem for accepted Dirichlet columns. -/
theorem sixReference_baseline_equal_total_reference
    (C : Finset (Fin 6))
    (hC : C ∈ bottomClasses sixChecked.baseline)
    (x : Fin 6) :
    sixReference.baseline.weight C x =
      (referenceMenuCertificate sixRaw sixChecked).baseline.weight C x := by
  have hSix := (checkMenu_sound sixRaw sixChecked
    sixReference sixReference_valid).1
  have hOne : checkDirichlet sixChecked.baseline sixReference.baseline = true :=
    checkDirichlet_complete sixChecked.baseline sixReference.baseline hSix
  have hTotal := referenceDirichlet_check_true sixChecked.baseline
  exact checked_class_column_unique sixChecked.baseline
    sixReference.baseline
    (referenceMenuCertificate sixRaw sixChecked).baseline
    hOne hTotal C hC x

/-- Each intervention has its own reference solution; no baseline
selector or certificate is reused for an intervened kernel. -/
theorem sixReference_member_equal_total_reference
    (i : Fin 6) (C : Finset (Fin 6))
    (hC : C ∈ bottomClasses (sixChecked.members i))
    (x : Fin 6) :
    (sixReference.members i).weight C x =
      ((referenceMenuCertificate sixRaw sixChecked).members i).weight C x := by
  have hSix := (checkMenu_sound sixRaw sixChecked
    sixReference sixReference_valid).2 i
  have hOne : checkDirichlet (sixChecked.members i)
      (sixReference.members i) = true :=
    checkDirichlet_complete (sixChecked.members i) (sixReference.members i) hSix
  have hTotal := referenceDirichlet_check_true (sixChecked.members i)
  exact checked_class_column_unique (sixChecked.members i)
    (sixReference.members i)
    ((referenceMenuCertificate sixRaw sixChecked).members i)
    hOne hTotal C hC x

/-- The original independently established Exact GR is the separate
premise for promoting the positive full/half/tiny margins to relative PR. -/
theorem six_original_baseline_exactGR :
    IsExactGeneratedRegime typedModel observedSpec observedReference :=
  observedExactGeneratedRegime

end
end C10
end ReverseSolver
end PermanssonResearch
