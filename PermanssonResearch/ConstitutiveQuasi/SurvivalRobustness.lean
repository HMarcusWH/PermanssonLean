import PermanssonResearch.ConstitutiveQuasi.PathOutput
import PermanssonLean.Regime.Persistence

/-!
# CQ-1: survival-event robustness

The frozen survivalProbability uses ENNReal, while the event-TV budget uses
real numbers. This module explicitly converts the finite-prefix event to a real
probability and bounds it without changing the definition of survival.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Survival through L transitions is the real mass of the prefix-survival
event under the canonical finite-prefix law. -/
theorem survivalProbability_toReal_eq_prefix
    (M : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (y : PermanssonLean.JointState S X) (L : ℕ) :
    (PermanssonLean.RegimeSpecification.survivalProbability M spec y L).toReal =
      (PermanssonLean.ProbabilitySupport.finitePrefixLaw M.inducedKernel y L).real
        (PermanssonLean.RegimeSpecification.prefixSurvivalSet spec L) := by
  unfold PermanssonLean.RegimeSpecification.survivalProbability
  rw [PermanssonLean.RegimeSpecification.survivesThroughSet_eq_preimage_prefix]
  rw [← Measure.map_apply (Preorder.measurable_frestrictLe L)
    (PermanssonLean.RegimeSpecification.measurableSet_prefixSurvivalSet spec L)]
  rw [pathLaw_finitePrefix_eq]
  rfl

/-- The survival-probability discrepancy obeys the same geometric prefix-TV
bound, for two models and the identical frozen regime region. -/
theorem survivalProbability_real_abs_le_geometric
    [MeasurableSpace.CountableOrCountablyGenerated
      (PermanssonLean.JointState S X) (PermanssonLean.JointState S X)]
    (M Mtilde : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hTV : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel Mtilde.inducedKernel δ)
    (y : PermanssonLean.JointState S X) (L : ℕ) :
    |(PermanssonLean.RegimeSpecification.survivalProbability M spec y L).toReal -
      (PermanssonLean.RegimeSpecification.survivalProbability Mtilde spec y L).toReal| ≤
      PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ L := by
  rw [survivalProbability_toReal_eq_prefix,
    survivalProbability_toReal_eq_prefix]
  exact (PermanssonLean.ProbabilitySupport.abs_measureReal_sub_le_eventTotalVariation
    (PermanssonLean.ProbabilitySupport.finitePrefixLaw M.inducedKernel y L)
    (PermanssonLean.ProbabilitySupport.finitePrefixLaw Mtilde.inducedKernel y L)
    (PermanssonLean.RegimeSpecification.measurableSet_prefixSurvivalSet spec L)).trans
    (PermanssonLean.ProbabilitySupport.finitePrefix_eventTotalVariation_le_geometric
      M.inducedKernel Mtilde.inducedKernel hδ0 hδ1 hTV y L)

/-- A real-valued baseline survival floor transfers to an approximate model
with the corresponding finite-prefix TV budget. -/
theorem finiteSurvival_lower_of_prefixTV
    [MeasurableSpace.CountableOrCountablyGenerated
      (PermanssonLean.JointState S X) (PermanssonLean.JointState S X)]
    (M Mtilde : PermanssonLean.StrategicWorldModel S X A)
    (spec : PermanssonLean.RegimeSpecification (PermanssonLean.JointState S X) H)
    (L : ℕ) (floor : ℝ)
    (hfloor : ∀ y ∈ spec.region,
      floor ≤ (PermanssonLean.RegimeSpecification.survivalProbability M spec y L).toReal)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hTV : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound
      M.inducedKernel Mtilde.inducedKernel δ) :
    ∀ y ∈ spec.region,
      floor - PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ L ≤
        (PermanssonLean.RegimeSpecification.survivalProbability Mtilde spec y L).toReal := by
  intro y hy
  have hdiff := survivalProbability_real_abs_le_geometric M Mtilde spec
    hδ0 hδ1 hTV y L
  have hleft := (abs_le.mp hdiff).2
  have hbase := hfloor y hy
  linarith

end ConstitutiveQuasi
end PermanssonResearch
