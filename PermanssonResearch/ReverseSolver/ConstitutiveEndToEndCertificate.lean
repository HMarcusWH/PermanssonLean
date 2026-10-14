import PermanssonResearch.ReverseSolver.ConstitutiveCertificateCheck
import PermanssonResearch.ReverseSolver.MenuMarginOptimization
import PermanssonLean.Regime.UniformPermansson
import Mathlib.Tactic

/-!
# C10 — original PR logical gates (no surrogate definitions)

This module exposes an important distinction: ZERO original uniform
constitutive margin refutes original uniform-relative PR directly, even
without an Exact-GR certificate. A positive margin proves uniform strategic
constitution but not original PR without the separately supplied original
Exact-GR certificate. Neither computational receipt acceptance nor unknown
baseline status is itself a positive PR certificate.

The generic numerical-to-original margin equality is NOT asserted here:
the genuine native infinite-path and Dirichlet uniqueness bridge remains
an independent C10 proof obligation.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open PermanssonResearch.MultipleLimit.FrozenObservedEvent

variable {S X A : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [TopologicalSpace S] [TopologicalSpace X]

/-- A theorem about the UNCHANGED ORIGINAL definition: numerical zero,
once transported to the actual original margin, is incompatible with
original uniform relative PR. No baseline GR premise is needed. -/
theorem original_zero_margin_excludes_uniformPR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (hzero : constitutiveMargin M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J = 0) :
    ¬ IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true) B₁ J := by
  intro hpr
  have hp := uniformRelativePR_margin_pos M spec m F
    (eventuallyObservedProperty spec.descriptor true) B₁ J hpr
  rw [hzero] at hp
  exact (lt_irrefl (0 : ℝ)) hp

/-- Positive original margin is already a meaningful uniform-constitution
claim without any attempt to infer Exact GR from numerical evidence. -/
theorem original_positive_margin_is_uniform_constitution
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (hpositive : 0 < constitutiveMargin M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J) :
    IsUniformlyStrategicallyConstitutive M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J :=
  (uniformlyConstitutive_iff_margin_pos M spec F
    (eventuallyObservedProperty spec.descriptor true) B₁ J).mpr hpositive

/-- A genuine ORIGINAL Exact-GR proof, not a status string, promotes the
positive original margin to the original relative PR predicate. -/
theorem original_positive_margin_plus_exactGR
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (hGR : IsExactGeneratedRegime M spec m)
    (hpositive : 0 < constitutiveMargin M spec F
      (eventuallyObservedProperty spec.descriptor true) B₁ J) :
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true) B₁ J :=
  ⟨hGR, original_positive_margin_is_uniform_constitution
    M spec F B₁ J hpositive⟩

end C10
end ReverseSolver
end PermanssonResearch