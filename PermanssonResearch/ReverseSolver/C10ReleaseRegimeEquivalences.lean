import PermanssonResearch.ReverseSolver.C10ReceiptSemantics
import PermanssonResearch.ReverseSolver.MenuConstitutionClassification
import Mathlib.Tactic

/-!
# C10 — exact checked receipt ↔ original relative PR and C9 support

The numeric-to-original-margin transport was already proved by C10.
This module completes the two-sided REGIME layer without supplying a
fake baseline certificate: positivity ↔ original uniform relative PR
needs the actual original Exact GR proof. Support eligibility also needs
the literal original C9 `almostSureWeak` convergence-mode hypothesis.

No statement is about unlisted interventions or an external model.
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
open MenuConstitutionClassification
open PermanssonResearch.MultipleLimit.FrozenObservedEvent
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- With an ACTUAL original Exact GR proof, receipt margin positivity is
equivalent to the untouched original uniform-relative PR predicate.
Neither numerical positivity alone nor a JSON flag creates hGR. -/
theorem checkedFullReceipt_positive_iff_original_uniformPR_of_exactGR
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
    (hGR : IsExactGeneratedRegime
      (realizedModel checked.baseline) spec reference)
    (i : Fin m) :
    0 < receipt.core.reportedMargin i ↔
      IsUniformGeneralizedPermanssonRegimeRelative
        (realizedModel checked.baseline) spec reference
        (researchActionFamily checked.baseline)
        (eventuallyObservedProperty spec.descriptor true) B₁
        (rationalStrategicIntervention checked.baseline
          (checked.members i)) := by
  constructor
  · intro hp
    exact checkedFullReceipt_positive_plus_exactGR
      raw checked receipt hc spec reference B₁
      hDescriptor hComparison i hp hGR
  · intro hPR
    have hpos : 0 < constitutiveMargin
        (realizedModel checked.baseline) spec
        (researchActionFamily checked.baseline)
        (eventuallyObservedProperty spec.descriptor true) B₁
        (rationalStrategicIntervention checked.baseline
          (checked.members i)) :=
      uniformRelativePR_margin_pos
        (realizedModel checked.baseline) spec reference
        (researchActionFamily checked.baseline)
        (eventuallyObservedProperty spec.descriptor true) B₁
        (rationalStrategicIntervention checked.baseline
          (checked.members i)) hPR
    have hEq := checkedFullReceipt_originalMargin
      raw checked receipt hc spec B₁ hDescriptor hComparison i
    change 0 < menuConstitutiveMargin
      (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) i at hpos
    rw [hEq] at hpos
    exact_mod_cast hpos

/-- The existing original C9 equivalence is retained verbatim for this
fully constructed typed menu. Literal mode is required; hGR is kept as
a genuine conjunct rather than a claimed Boolean evidence status. -/
theorem checkedFullReceipt_originalPR_iff_exactGR_and_support_of_literalMode
    {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (reference : Measure (JointState Unit (Fin n)))
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState Unit (Fin n)) Bool)
    (i : Fin m) :
    IsUniformGeneralizedPermanssonRegimeRelative
      (realizedModel checked.baseline) spec reference
      (researchActionFamily checked.baseline)
      (eventuallyObservedProperty spec.descriptor true) B₁
      (rationalStrategicIntervention checked.baseline
        (checked.members i)) ↔
    IsExactGeneratedRegime
      (realizedModel checked.baseline) spec reference ∧
    menuSupportEligible (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) i := by
  exact listed_uniformPR_iff_exactGR_and_support
    (realizedModel checked.baseline) spec reference
    (researchActionFamily checked.baseline) B₁
    (realizedNumericMenu raw checked) hmode i

/-- Under genuine original Exact GR AND literal C9 observation mode,
strictly positive exact receipt margin iff the original opposing-class
support eligibility of the EXACT same intervention from every B₁ start. -/
theorem checkedFullReceipt_positive_iff_support_of_exactGR_literalMode
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
    (hGR : IsExactGeneratedRegime
      (realizedModel checked.baseline) spec reference)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState Unit (Fin n)) Bool)
    (i : Fin m) :
    0 < receipt.core.reportedMargin i ↔
      menuSupportEligible (realizedModel checked.baseline) spec
        (researchActionFamily checked.baseline) B₁
        (realizedNumericMenu raw checked) i := by
  have hC9 := margin_pos_iff_support_of_exactGR
    (realizedModel checked.baseline) spec reference
    (researchActionFamily checked.baseline) B₁
    (realizedNumericMenu raw checked) hGR hmode i
  have hEq := checkedFullReceipt_originalMargin
    raw checked receipt hc spec B₁ hDescriptor hComparison i
  constructor
  · intro hp
    apply hC9.mp
    rw [hEq]
    exact_mod_cast hp
  · intro hEligible
    have hReal := hC9.mpr hEligible
    rw [hEq] at hReal
    exact_mod_cast hReal

/-- Even without hGR, literal-mode support INELIGIBILITY rules out
original relative PR for that particular listed candidate; this does
NOT imply a zero numerical margin without hGR. -/
theorem checkedFullReceipt_support_ineligible_not_uniformPR_of_literalMode
    {n m : ℕ} [NeZero n]
    (raw : RawInput n m) (checked : CheckedInput raw)
    (spec : RegimeSpecification (JointState Unit (Fin n)) Bool)
    (reference : Measure (JointState Unit (Fin n)))
    (B₁ : ConstitutiveComparisonSet (realizedModel checked.baseline) spec)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState Unit (Fin n)) Bool)
    (i : Fin m)
    (hNoSupport : ¬ menuSupportEligible
      (realizedModel checked.baseline) spec
      (researchActionFamily checked.baseline) B₁
      (realizedNumericMenu raw checked) i) :
    ¬ IsUniformGeneralizedPermanssonRegimeRelative
      (realizedModel checked.baseline) spec reference
      (researchActionFamily checked.baseline)
      (eventuallyObservedProperty spec.descriptor true) B₁
      (rationalStrategicIntervention checked.baseline
        (checked.members i)) := by
  intro hPR
  have h := (checkedFullReceipt_originalPR_iff_exactGR_and_support_of_literalMode
    raw checked spec reference B₁ hmode i).mp hPR
  exact hNoSupport h.2

end
end C10
end ReverseSolver
end PermanssonResearch
