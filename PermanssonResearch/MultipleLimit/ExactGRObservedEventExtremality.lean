import PermanssonResearch.MultipleLimit.FiniteObservedClassDirac
import PermanssonResearch.MultipleLimit.FiniteObservedEventMass
import PermanssonResearch.MultipleLimit.FiniteObservedLimitUniqueness
import Mathlib.Tactic

/-!
# C8-04 — original Exact GR forces a 0/1 eventual-true response

The frozen baseline is an ORIGINAL Exact Generated Regime, and the
convergence mode is LITERALLY almostSureWeak. The target Bool occupation
law need not itself be a Dirac measure. When it is delta_true the
eventually-true path event has probability one throughout the basin;
for any other target, including genuinely mixed laws, its probability
is zero. Without literal mode, no such implication is claimed.

The proof combines C3's a.s. canonical equality to the frozen target,
C7's a.s. class/event characterization, and exact class stationarity
support. It does not assume empirical identification or transfer a
baseline class selector to an intervened kernel.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactGRObservedEventExtremality

set_option autoImplicit false
attribute [local instance] Classical.propDecidable

open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteCanonicalPath
open FiniteOccupationRandomLaw
open FiniteObservedLimitUniqueness
open CanonicalClassSelector
open ClassDescriptorSelectionLaw
open FiniteObservedClassSupport
open FiniteObservedClassDirac
open FiniteObservedEventMass
open FrozenObservedEvent

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

/-- From one ORIGINAL Exact-GR initial basin state, the genuine
canonical event coincides almost surely with the fixed target
being the TRUE Dirac law. No assertion on arbitrary exceptional
trajectories or on custom convergence modes. -/
theorem canonical_event_iff_target_dirac_ae
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    (hGR : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool)
    (y : JointState S X) (hy : y ∈ spec.basin) :
    ∀ᵐ w ∂canonicalPathLaw M.inducedKernel (Measure.dirac y),
      (w ∈ eventuallyObserved spec.descriptor true ↔
        spec.target = diracProba true) := by
  have hadmiss : IsAdmissibleInitialLaw spec (diracProba y) :=
    (dirac_admissible_iff spec y).mpr hy
  have hLimit := exactGR_observedOccupationLimit_ae
    M spec m hGR hmode (diracProba y) hadmiss
  change ∀ᵐ w ∂canonicalPathLaw M.inducedKernel (Measure.dirac y),
    observedStationaryForClass M.inducedKernel spec.descriptor
      (selectedRepresentative M.inducedKernel w) = spec.target at hLimit
  filter_upwards
    [hLimit,
     eventuallyObserved_iff_selectedGood_ae
       M.inducedKernel spec.descriptor (diracProba y)]
    with w hstationary hevent
  have hrep : selectedRepresentative M.inducedKernel w ∈
      recurrentRepresentatives M.inducedKernel :=
    selectedRepresentative_mem M.inducedKernel w
  have hdirac := observed_stationary_trueDirac_iff_allTrue
    M.inducedKernel spec.descriptor
    (selectedRepresentative M.inducedKernel w) hrep
  constructor
  · intro hobs
    have hgood := hevent.mp hobs
    exact hstationary.symm.trans (hdirac.mpr hgood)
  · intro htarget
    have heq : observedStationaryForClass M.inducedKernel
      spec.descriptor (selectedRepresentative M.inducedKernel w) =
        diracProba true :=
      hstationary.trans htarget
    exact hevent.mpr (hdirac.mp heq)

/-- G3 in exact canonical probability form, for EVERY original
basin state and without presuming that the target is Dirac. -/
theorem baseline_event_probability_extremal
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) Bool)
    (m : Measure (JointState S X))
    (hGR : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) Bool)
    (y : JointState S X) (hy : y ∈ spec.basin) :
    (canonicalPathLaw M.inducedKernel (Measure.dirac y))
      (eventuallyObserved spec.descriptor true) =
        if spec.target = diracProba true then 1 else 0 := by
  classical
  let P := canonicalPathLaw M.inducedKernel (Measure.dirac y)
  have hiff := canonical_event_iff_target_dirac_ae
    M spec m hGR hmode y hy
  by_cases htarget : spec.target = diracProba true
  · rw [if_pos htarget]
    have hset :
        eventuallyObserved spec.descriptor true =ᵐ[P]
          (Set.univ : Set (ℕ → JointState S X)) := by
      filter_upwards [hiff] with w hw
      apply propext
      constructor
      · intro _
        trivial
      · intro _
        exact hw.mpr htarget
    exact (measure_congr hset).trans measure_univ
  · rw [if_neg htarget]
    have hset :
        eventuallyObserved spec.descriptor true =ᵐ[P]
          (∅ : Set (ℕ → JointState S X)) := by
      filter_upwards [hiff] with w hw
      apply propext
      constructor
      · intro hv
        exact (htarget (hw.mp hv)).elim
      · intro hv
        exact False.elim (by simpa using hv)
    exact (measure_congr hset).trans measure_empty

end ExactGRObservedEventExtremality
end MultipleLimit
end PermanssonResearch
