import PermanssonResearch.ReverseSolver.C10FullReceipt
import PermanssonResearch.ReverseSolver.TypedOriginalMenuMargin
import PermanssonResearch.ReverseSolver.ConstitutiveEndToEndCertificate
import Mathlib.Tactic

/-!
# C10 — a checked full rational receipt is the genuine original typed margin

The numerical soundness chain and the typed original path-law bridge remain
separate. These theorems require the actual global descriptor agreement and
the COMPLETE original B₁ set, not a JSON status flag. Original Exact GR is
only required for positive Permansson-regime promotion.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false
open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteStrategicRealization
open FrozenConstitutiveMenu
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

private theorem full_receipt_core_checked {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m)
    (hc : checkFullReceipt raw checked receipt = true) :
    checkReceipt raw checked receipt.core = true := by
  unfold checkFullReceipt at hc
  exact (andB_eq_true_iff _ _).mp hc |>.1

/-- The semantic bridge needs the checked MENU equations, not merely
the Boolean acceptance of the encompassing receipt. -/
private theorem full_receipt_menu_checked {n m : ℕ}
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m)
    (hc : checkFullReceipt raw checked receipt = true) :
    checkMenu raw checked receipt.core.classTables = true := by
  have hCore := full_receipt_core_checked raw checked receipt hc
  unfold checkReceipt at hCore
  exact ((andB_eq_true_iff _ _).mp hCore).1

/-- Every accepted full receipt reports the UNMODIFIED original real
constitutive margin over the complete original typed comparison set. -/
theorem checkedFullReceipt_originalMargin {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m)
    (hc : checkFullReceipt raw checked receipt = true)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hDescriptor : ∀ x : Fin n,
      spec.descriptor (decode x) = raw.descriptor x)
    (hComparison : ∀ x : Fin n,
      x ∈ raw.comparison ↔ decode x ∈ B₁.states)
    (i : Fin m) :
    menuConstitutiveMargin (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) i =
        (receipt.core.reportedMargin i : ℝ) := by
  have hChecked := full_receipt_menu_checked raw checked receipt hc
  have hFields := (checkFullReceipt_sound raw checked receipt hc).1
  calc
    menuConstitutiveMargin (realizedModel checked.baseline) spec
        (researchActionFamily checked.baseline) B₁
        (realizedNumericMenu raw checked) i =
          (numericalMargin raw checked receipt.core.classTables i : ℝ) :=
      realized_numeric_menu_margin raw checked receipt.core.classTables
        hChecked spec B₁ hDescriptor hComparison i
    _ = (receipt.core.reportedMargin i : ℝ) :=
      congrArg (fun q : ℚ => (q : ℝ)) (hFields.2.1 i).symm

/-- A checked receipt's selected member beats every single member of the
ORIGINAL frozen typed menu, not merely a graph-eligible sublist. -/
theorem checkedFullReceipt_originalSelectedDominates
    {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m)
    (hc : checkFullReceipt raw checked receipt = true)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hDescriptor : ∀ x : Fin n,
      spec.descriptor (decode x) = raw.descriptor x)
    (hComparison : ∀ x : Fin n,
      x ∈ raw.comparison ↔ decode x ∈ B₁.states)
    (i : Fin m) :
    menuConstitutiveMargin (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) i ≤
    menuConstitutiveMargin (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) receipt.core.selectedIndex := by
  have hChecked := full_receipt_menu_checked raw checked receipt hc
  have hFields := (checkFullReceipt_sound raw checked receipt hc).1
  simpa only [hFields.2.2.1] using
    realized_numeric_menu_selected_dominates raw checked
      receipt.core.classTables hChecked spec B₁
      hDescriptor hComparison i

/-- Exact zero excludes the ORIGINAL uniform relative PR, even if
there is no proof of baseline Exact GR and regardless of any status string. -/
theorem checkedFullReceipt_zero_excludes_uniformPR
    {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m)
    (hc : checkFullReceipt raw checked receipt = true)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (reference : Measure (JointState Unit (Fin n)))
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hDescriptor : ∀ x : Fin n,
      spec.descriptor (decode x) = raw.descriptor x)
    (hComparison : ∀ x : Fin n,
      x ∈ raw.comparison ↔ decode x ∈ B₁.states)
    (i : Fin m) (hzero : receipt.core.reportedMargin i = 0) :
    ¬ IsUniformGeneralizedPermanssonRegimeRelative
      (realizedModel checked.baseline) spec reference
      (researchActionFamily checked.baseline)
      (eventuallyObservedProperty spec.descriptor true) B₁
      (rationalStrategicIntervention checked.baseline (checked.members i)) := by
  have hEq := checkedFullReceipt_originalMargin raw checked
    receipt hc spec B₁ hDescriptor hComparison i
  have hOriginalZero :
      constitutiveMargin (realizedModel checked.baseline) spec
        (researchActionFamily checked.baseline)
        (eventuallyObservedProperty spec.descriptor true) B₁
        (rationalStrategicIntervention checked.baseline (checked.members i)) = 0 := by
    change menuConstitutiveMargin (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) i = 0
    rw [hEq, hzero]
    norm_num
  exact original_zero_margin_excludes_uniformPR
    (realizedModel checked.baseline) spec reference
    (researchActionFamily checked.baseline) B₁
    (rationalStrategicIntervention checked.baseline (checked.members i))
    hOriginalZero


/-- An exact zero global optimum rules out uniform original PR status for
EVERY listed typed intervention, including when baseline Exact GR has not
been certified. This says nothing about unlisted family members. -/
theorem checkedFullReceipt_all_zero_listed_not_uniformPR
    {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m)
    (hc : checkFullReceipt raw checked receipt = true)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (reference : Measure (JointState Unit (Fin n)))
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hDescriptor : ∀ x : Fin n,
      spec.descriptor (decode x) = raw.descriptor x)
    (hComparison : ∀ x : Fin n,
      x ∈ raw.comparison ↔ decode x ∈ B₁.states)
    (hZeroMax : receipt.core.reportedOptimum = 0)
    (i : Fin m) :
    ¬ IsUniformGeneralizedPermanssonRegimeRelative
      (realizedModel checked.baseline) spec reference
      (researchActionFamily checked.baseline)
      (eventuallyObservedProperty spec.descriptor true) B₁
      (rationalStrategicIntervention checked.baseline (checked.members i)) := by
  have hCore := full_receipt_core_checked raw checked receipt hc
  have hBound := checked_receipt_global_max
    raw checked receipt.core hCore i
  rw [hZeroMax] at hBound
  have hFields := (checkFullReceipt_sound raw checked receipt hc).1
  have hNonneg : (0 : ℚ) ≤ receipt.core.reportedMargin i := by
    rw [hFields.2.1 i]
    change (0 : ℚ) ≤ raw.comparison.inf'
      checked.comparisonNonempty (numericalEffect raw receipt.core.classTables i)
    apply Finset.le_inf'
    intro x _
    exact numericalEffect_nonneg raw receipt.core.classTables i x
  have hZero : receipt.core.reportedMargin i = 0 :=
    le_antisymm hBound hNonneg
  exact checkedFullReceipt_zero_excludes_uniformPR
    raw checked receipt hc spec reference B₁
    hDescriptor hComparison i hZero

/-- Positive original PR requires the genuine Original Exact-GR proof;
a positive numerical value alone never supplies that missing premise. -/
theorem checkedFullReceipt_positive_plus_exactGR
    {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (receipt : FullReceipt n m)
    (hc : checkFullReceipt raw checked receipt = true)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (reference : Measure (JointState Unit (Fin n)))
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hDescriptor : ∀ x : Fin n,
      spec.descriptor (decode x) = raw.descriptor x)
    (hComparison : ∀ x : Fin n,
      x ∈ raw.comparison ↔ decode x ∈ B₁.states)
    (i : Fin m) (hpositive : 0 < receipt.core.reportedMargin i)
    (hGR : IsExactGeneratedRegime
      (realizedModel checked.baseline) spec reference) :
    IsUniformGeneralizedPermanssonRegimeRelative
      (realizedModel checked.baseline) spec reference
      (researchActionFamily checked.baseline)
      (eventuallyObservedProperty spec.descriptor true) B₁
      (rationalStrategicIntervention checked.baseline (checked.members i)) := by
  have hEq := checkedFullReceipt_originalMargin raw checked
    receipt hc spec B₁ hDescriptor hComparison i
  have hOriginalPositive :
      0 < constitutiveMargin (realizedModel checked.baseline) spec
        (researchActionFamily checked.baseline)
        (eventuallyObservedProperty spec.descriptor true) B₁
        (rationalStrategicIntervention checked.baseline (checked.members i)) := by
    change 0 < menuConstitutiveMargin (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) i
    rw [hEq]
    exact_mod_cast hpositive
  exact original_positive_margin_plus_exactGR
    (realizedModel checked.baseline) spec reference
    (researchActionFamily checked.baseline) B₁
    (rationalStrategicIntervention checked.baseline (checked.members i))
    hGR hOriginalPositive

end
end C10
end ReverseSolver
end PermanssonResearch
