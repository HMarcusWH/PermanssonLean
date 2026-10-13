import PermanssonResearch.MultipleLimit.OppositeClassConstitutiveMargin
import PermanssonResearch.MultipleLimit.ObservedSupportInvariance
import Mathlib.Tactic

/-!
# C8-07 — same-support invariance of qualitative original PR

The original model, exact-GR specification, frozen Boolean property,
comparison set and admissible intervention family stay fixed. Two
DIFFERENT eligible strategic interventions with equal positive support
for their induced kernels have the same YES/NO original uniform PR
classification, under literal almostSureWeak mode.

No claim is made that their empirical class weights, path laws,
stationary measures, or numerical constitutive margins are equal.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedObservedSupportInvariance

set_option autoImplicit false

open PermanssonLean
open PermanssonLean.RegimeSpecification
open OppositeClassConstitutiveMargin
open ObservedSupportInvariance
open FrozenObservedEvent

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y]
variable [DecidableEq Y] [StandardBorelSpace Y]

theorem opposingReachability_iff_of_sameSupport
    (K L : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel L]
    (h : Y → Bool) (ν : ProbabilityMeasure Bool) (y : Y)
    (hs : SamePositiveSupport K L) :
    OpposingClassReachable K h ν y ↔
      OpposingClassReachable L h ν y := by
  by_cases ht : ν = diracProba true
  · simp only [OpposingClassReachable, if_pos ht]
    exact badReachability_iff K L hs h y
  · simp only [OpposingClassReachable, if_neg ht]
    exact goodReachability_iff K L hs h y

variable {S X A : Type*}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [Fintype (JointState S X)] [Nonempty (JointState S X)]
variable [DecidableEq (JointState S X)]
variable [MeasurableSingletonClass (JointState S X)]
variable [DiscreteTopology (JointState S X)]
variable [OpensMeasurableSpace (JointState S X)]
variable [StandardBorelSpace (JointState S X)]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- G7 in the ORIGINAL unweakened quantitative PR predicate. Exactly
matching support graphs of the TWO eligible intervened induced kernels
preserve qualitative constitution; neither a shared class-selection
law nor equality of numerical effects is asserted. -/
theorem original_uniformPR_iff_of_same_intervened_support
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    {Component : Type*}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J₁ J₂ : AdmissibleStrategicIntervention F)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool)
    (hs : SamePositiveSupport
      J₁.intervention.apply.inducedKernel
      J₂.intervention.apply.inducedKernel) :
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true) B₁ J₁ ↔
    IsUniformGeneralizedPermanssonRegimeRelative M spec m F
      (eventuallyObservedProperty spec.descriptor true) B₁ J₂ := by
  rw [original_uniformRelativePR_iff_opposingReachability
    M spec m F B₁ J₁ hmode]
  rw [original_uniformRelativePR_iff_opposingReachability
    M spec m F B₁ J₂ hmode]
  constructor
  · rintro ⟨hGR, hreach⟩
    refine ⟨hGR, ?_⟩
    intro y hy
    exact (opposingReachability_iff_of_sameSupport
      J₁.intervention.apply.inducedKernel
      J₂.intervention.apply.inducedKernel
      spec.descriptor spec.target y hs).mp (hreach y hy)
  · rintro ⟨hGR, hreach⟩
    refine ⟨hGR, ?_⟩
    intro y hy
    exact (opposingReachability_iff_of_sameSupport
      J₁.intervention.apply.inducedKernel
      J₂.intervention.apply.inducedKernel
      spec.descriptor spec.target y hs).mpr (hreach y hy)

end TypedObservedSupportInvariance
end MultipleLimit
end PermanssonResearch
