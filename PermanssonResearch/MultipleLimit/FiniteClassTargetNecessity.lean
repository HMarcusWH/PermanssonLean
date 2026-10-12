import PermanssonResearch.MultipleLimit.FiniteObservedLimitUniqueness
import PermanssonResearch.MultipleLimit.BasinFamily
import Mathlib.Tactic

/-!
# C54-02 — positive class selection forces the frozen Exact GR target

A selected recurrent class of nonzero actual canonical path probability
cannot carry an observed stationary law different from an almost-surely
fixed original regime target. No lower selection-weight cutoff, stationarity
of the initial law, or aperiodicity is used.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteClassTargetNecessity

open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteCanonicalPath
open FiniteObservedLimitUniqueness
open FiniteOccupationRandomLaw
open ClassDescriptorSelectionLaw
open CanonicalClassSelector
open BasinFamily

variable {S X A H : Type*}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
variable [TopologicalSpace S] [TopologicalSpace X]
variable [TopologicalSpace H] [BorelSpace H]
variable [T2Space (ProbabilityMeasure H)]
variable [Fintype (JointState S X)] [Nonempty (JointState S X)]
variable [DecidableEq (JointState S X)]
variable [MeasurableSingletonClass (JointState S X)]
variable [DiscreteTopology (JointState S X)]
variable [OpensMeasurableSpace (JointState S X)]
variable [StandardBorelSpace (JointState S X)]

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

/-- Any genuine positive-mass canonical class-selection event from a
point in the basin must select a stationary descriptor law equal to
the originally prescribed Exact GR target. -/
theorem exactGR_class_target_of_positive_selection
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (hExact : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H)
    (y : JointState S X) (hy : y ∈ spec.basin)
    (i : JointState S X)
    (hpos : (canonicalPathLaw M.inducedKernel (Measure.dirac y))
      ((selectedRepresentative M.inducedKernel) ⁻¹' {i}) ≠ 0) :
    observedStationaryForClass M.inducedKernel spec.descriptor i =
      spec.target := by
  by_contra hne
  have hAdm : IsAdmissibleInitialLaw spec (diracProba y) :=
    (dirac_admissible_iff spec y).mpr hy
  have hAE := exactGR_observedOccupationLimit_ae
    M spec m hExact hmode (diracProba y) hAdm
  change ∀ᵐ w ∂canonicalPathLaw M.inducedKernel (Measure.dirac y),
    observedOccupationLimit M.inducedKernel spec.descriptor w =
      spec.target at hAE
  rw [ae_iff] at hAE
  have hsubset :
      (selectedRepresentative M.inducedKernel) ⁻¹' ({i} : Set (JointState S X)) ⊆
      {w : ℕ → JointState S X |
        observedOccupationLimit M.inducedKernel spec.descriptor w ≠
          spec.target} := by
    intro w hw
    have hsel : selectedRepresentative M.inducedKernel w = i := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hw
    change observedStationaryForClass M.inducedKernel spec.descriptor
      (selectedRepresentative M.inducedKernel w) ≠ spec.target
    rw [hsel]
    exact hne
  have hzero :
      (canonicalPathLaw M.inducedKernel (Measure.dirac y))
        ((selectedRepresentative M.inducedKernel) ⁻¹' {i}) = 0 :=
    measure_mono_null hsubset hAE
  exact hpos hzero

/-- Membership in the C2 reachable-family filter gives a point start
inside the frozen basin with nonzero genuine selection probability. -/
theorem exactGR_common_target_on_reachable
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h41 : Assumption41 M spec m)
    (hinv : IsExactlyInvariant M spec)
    (hExact : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H) :
    ∀ i ∈ reachableRepresentatives M.inducedKernel H
        (FiniteExactGRRecovery.frozenFamilyOfExactSpec M spec m h41 hinv),
      observedStationaryForClass M.inducedKernel spec.descriptor i =
        spec.target := by
  intro i hi
  have hf :
      i ∈ (recurrentRepresentatives M.inducedKernel).filter
        (fun z => ∃ y ∈ spec.basin,
          canonicalPathLaw M.inducedKernel (Measure.dirac y)
            ((selectedRepresentative M.inducedKernel) ⁻¹' {z}) ≠ 0) := hi
  obtain ⟨_, y, hy, hpos⟩ := Finset.mem_filter.mp hf
  exact exactGR_class_target_of_positive_selection
    M spec m hExact hmode y hy i hpos

/-- The actual family of positively selected classes is a function
of the frozen basin, not of its descriptor or auxiliary certificate
proof fields. This is used for target-replacement obstruction. -/
theorem reachableRepresentatives_eq_of_basin_eq
    {Y H' : Type*} [MeasurableSpace Y] [Fintype Y]
    [MeasurableSingletonClass Y] [Nonempty Y]
    [MeasurableSpace H']
    (K : Kernel Y Y) [IsMarkovKernel K]
    (F G : FrozenBasinFamily K H')
    (hbasin : F.basin = G.basin) :
    reachableRepresentatives K H' F =
      reachableRepresentatives K H' G := by
  classical
  simp [reachableRepresentatives, hbasin]

end FiniteClassTargetNecessity
end MultipleLimit
end PermanssonResearch
