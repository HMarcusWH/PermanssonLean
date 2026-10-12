import PermanssonResearch.MultipleLimit.FiniteOccupationMeasureBridge
import PermanssonResearch.MultipleLimit.ClassDescriptorOccupationBridge
import PermanssonResearch.MultipleLimit.ClassDescriptorSelectionLaw
import Mathlib.Tactic

/-!
# C53-07 — the actual random occupation limit and its complete law

A measure-valued class selector is not enough: this module first proves
that it is the a.s. weak limit of the REAL physical finite empirical
occupations under the genuine infinite canonical Markov path law.
Only THEN may its exact finite Dirac-mixture law be interpreted as the
distribution of the empirical random limit.

The descriptor is frozen before taking limits; non-injective descriptors
are allowed and observable class atoms can coincide. No stationary
barycenter is substituted for a pathwise random limit.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteOccupationRandomLaw

open FiniteCanonicalPath
open KernelCommunication
open CanonicalClassSelector
open ClassStationarySelectionLaw
open ClassDescriptorSelectionLaw
open FiniteStateOccupation
open FiniteOccupationMeasureBridge
open ClassDescriptorOccupationBridge

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y] [DecidableEq Y]
variable [TopologicalSpace Y] [DiscreteTopology Y]
variable [OpensMeasurableSpace Y] [StandardBorelSpace Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- The unique stationary probability of the recurrent class selected
on the actual canonical infinite trajectory. Its existence and
uniqueness have already been derived classwise. -/
noncomputable def physicalOccupationLimit (w : ℕ → Y) :
    ProbabilityMeasure Y :=
  stationaryForSet K (CommunicatingClass K (selectedRepresentative K w))

/-- GENUINE a.s. weak convergence of finite empirical ProbabilityMeasure,
under arbitrary initial law, without chain irreducibility or aperiodicity. -/
theorem physicalOccupationLimit_ae_correct
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n : ℕ =>
        empiricalOccupation w (n+1) (Nat.succ_pos n))
      atTop (𝓝 (physicalOccupationLimit K w)) := by
  exact canonical_physical_occupation_ae_limit K μ

theorem physicalOccupationLimit_measurable :
    Measurable (physicalOccupationLimit K) :=
  (classStationaryAssignment_measurable K).comp
    (selectedRepresentative_measurable K)

/-- WHOLE law of the proven a.s. physical occupation limit:
Dirac atoms at class stationary probabilities with actual canonical
entry weights. It is not a one-time marginal or a barycenter. -/
theorem physicalOccupationLimit_full_law
    (μ : ProbabilityMeasure Y) :
    (canonicalPathLaw K μ.toMeasure).map
      (physicalOccupationLimit K) =
      ∑ i ∈ recurrentRepresentatives K,
        (canonicalPathLaw K μ.toMeasure)
          ((selectedRepresentative K) ⁻¹' {i}) •
          Measure.dirac (stationaryForSet K
            (CommunicatingClass K i)) := by
  exact stationarySelection_full_law K μ

variable {H : Type*} [MeasurableSpace H] [TopologicalSpace H]
variable [BorelSpace H]

/-- The frozen observed random occupation limit is the pushforward of
the proven physical limit by the PREDECLARED descriptor. -/
noncomputable def observedOccupationLimit (h : Y → H)
    (w : ℕ → Y) : ProbabilityMeasure H :=
  (physicalOccupationLimit K w).map h

/-- A.s. weak convergence for arbitrary frozen descriptors. Finite
discrete physical topology makes every descriptor continuous; there
is no injectivity requirement. -/
theorem observedOccupationLimit_ae_correct
    (μ : ProbabilityMeasure Y) (h : Y → H) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto
        (fun n : ℕ =>
          (empiricalOccupation w (n+1)
            (Nat.succ_pos n)).map h)
        atTop (𝓝 (observedOccupationLimit K h w)) := by
  filter_upwards [physicalOccupationLimit_ae_correct K μ] with w hw
  exact finite_discrete_descriptor_limit h w
    (physicalOccupationLimit K w) hw

theorem observedOccupationLimit_measurable (h : Y → H) :
    Measurable (observedOccupationLimit K h) := by
  have heq : observedOccupationLimit K h =
      fun w : ℕ → Y =>
        observedStationaryForClass K h (selectedRepresentative K w) := rfl
  rw [heq]
  exact (observedStationaryAssignment_measurable K h).comp
    (selectedRepresentative_measurable K)

/-- WHOLE law of actual observed occupation limits. Classes with equal
descriptor pushforwards contribute to the same Dirac atom, and their
weights add exactly as in the earlier aggregation lemma. -/
theorem observedOccupationLimit_full_law
    (μ : ProbabilityMeasure Y) (h : Y → H) :
    (canonicalPathLaw K μ.toMeasure).map
        (observedOccupationLimit K h) =
      ∑ i ∈ recurrentRepresentatives K,
        (canonicalPathLaw K μ.toMeasure)
          ((selectedRepresentative K) ⁻¹' {i}) •
          Measure.dirac (observedStationaryForClass K h i) := by
  exact selected_observed_stationary_full_law K μ h

end FiniteOccupationRandomLaw
end MultipleLimit
end PermanssonResearch
