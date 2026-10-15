import PermanssonResearch.RegimeExit.SwitchRetention
import Mathlib.Tactic

/-!
# C-Exit B — exact probability of a successful retained switch

This module closes the probabilistic RETENTION part of Proposition 4.2f
on the actual canonical path law. It does not assume a stopped-path
restart law or assert post-entry occupation convergence.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH uT uK
variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace T]
variable [TopologicalSpace S] [TopologicalSpace X]

/-- The first exit enters the new basin and the trajectory remains in
the new region for every subsequent time. The union is over *finite*
entry times and never evaluates Y at an infinite stopping index. -/
def successfullySwitchedAndRetained
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T) :
    Set (ℕ → JointState S X) :=
  ⋃ n : ℕ,
    firstExitAtDestination source n target.basin ∩
      ⋂ t : ℕ,
        if n + 1 ≤ t then
          (fun w : ℕ → JointState S X => w t) ⁻¹' target.region
        else Set.univ

theorem successfullySwitchedAndRetained_measurable
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T) :
    MeasurableSet (successfullySwitchedAndRetained source target) := by
  unfold successfullySwitchedAndRetained
  apply MeasurableSet.iUnion
  intro n
  apply MeasurableSet.inter
  · exact firstExitAtDestination_measurable source n target.basin
      target.basin_measurable
  · apply MeasurableSet.iInter
    intro t
    split_ifs with ht
    · exact target.region_measurable.preimage (measurable_pi_apply t)
    · exact MeasurableSet.univ

theorem successfullySwitchedAndRetained_subset_firstExit
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T) :
    successfullySwitchedAndRetained source target ⊆
      firstExitEverDestination source target.basin := by
  intro w hw
  rcases Set.mem_iUnion.mp hw with ⟨n, hn⟩
  exact Set.mem_iUnion.mpr ⟨n, hn.1⟩

/-- Under target Exact GR, the routed first-exit event and the event
with actual post-entry retention are equal almost everywhere. -/
theorem successful_switch_event_ae_eq_first_exit
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (μ : ProbabilityMeasure (JointState S X)) :
    successfullySwitchedAndRetained source target =ᵐ[
      J.intervention.apply.pathLaw μ.toMeasure]
        firstExitEverDestination source target.basin := by
  have h := switch_eventual_retention_ae M source target
    mSource mTarget F B₁ J cert μ
  filter_upwards [h] with w hw
  apply propext
  constructor
  · exact successfullySwitchedAndRetained_subset_firstExit source target
  · intro hevent
    obtain ⟨n, hn, hstay⟩ := hw hevent
    apply Set.mem_iUnion.mpr
    refine ⟨n, hn, ?_⟩
    apply Set.mem_iInter.mpr
    intro t
    split_ifs with ht
    · exact hstay t ht
    · exact Set.mem_univ _

/-- The probability of a real retained switch is EXACTLY the original
PR66 first-exit routing probability. -/
theorem successful_switch_retention_probability_eq_routing
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    J.intervention.apply.pathLaw (Measure.dirac y)
      (successfullySwitchedAndRetained source target) =
    exitRoutingInfinite J.intervention.apply source y target.basin := by
  have h := successful_switch_event_ae_eq_first_exit M source target
    mSource mTarget F B₁ J cert (diracProba y)
  change J.intervention.apply.pathLaw (diracProba y).toMeasure
    (successfullySwitchedAndRetained source target) = _
  rw [measure_congr h]
  exact (exitRoutingInfinite_eq_prob_exit_in J.intervention.apply
    source (ConstitutiveComparisonSet.states_subset_region M source B₁ hy)
    target.basin target.basin_measurable).symm

/-- V20.7 now bounds the TRUE retained-switch event, not just an
undischarged target-arrival predicate. -/
theorem successful_switch_retention_probability_ge
    (M : StrategicWorldModel S X A)
    (source : RegimeSpecification (JointState S X) H)
    (target : RegimeSpecification (JointState S X) T)
    (mSource mTarget : Measure (JointState S X))
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (B₁ : ConstitutiveComparisonSet M source)
    (J : AdmissibleStrategicIntervention F)
    (cert : CertifiedSwitchData M source target mSource mTarget F B₁ J)
    (eta : ℝ≥0∞)
    (hBound : SwitchRoutingBound M source target F B₁ J eta)
    {y : JointState S X} (hy : y ∈ B₁.states) :
    1 - eta ≤
      J.intervention.apply.pathLaw (Measure.dirac y)
        (successfullySwitchedAndRetained source target) := by
  rw [successful_switch_retention_probability_eq_routing M source target
    mSource mTarget F B₁ J cert hy]
  exact hBound.2 y hy

end PermanssonResearch.RegimeExit
