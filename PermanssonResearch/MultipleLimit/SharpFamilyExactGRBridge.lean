import PermanssonResearch.MultipleLimit.SharpObservedFamily
import PermanssonResearch.MultipleLimit.FiniteExactGRCharacterization
import Mathlib.Tactic

/-!
# C56-03 — conservative original Exact GR recovery from the sharp family

This is a new finite-family interface to the ALREADY PROVED C3 iff, not
a replacement for C3 or a new theorem about empirical identification.
All original Assumption 4.1 and exact-invariance gates remain explicit.
The convergence mode must LITERALLY be almostSureWeak; weak probability-
measure limits must be unique in the declared Hausdorff target topology.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace SharpFamilyExactGRBridge

open PermanssonLean
open PermanssonLean.RegimeSpecification
open BasinFamily
open SharpObservedFamily
open FiniteExactGRRecovery
open FiniteExactGRCharacterization
open ClassDescriptorSelectionLaw

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

/-- Under the original semantic gates, Exact GR is equivalent to
the sharp canonical observed-limit family being the SINGLE predeclared
target. A singleton consisting of the WRONG target is rejected.
No new original RegimeSpecification field is introduced. -/
theorem exactGR_iff_sharp_singleton
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h41 : Assumption41 M spec m)
    (hinv : IsExactlyInvariant M spec)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H) :
    IsExactGeneratedRegime M spec m ↔
      sharpObservedFamily M.inducedKernel
        (frozenFamilyOfExactSpec M spec m h41 hinv) =
          ({spec.target} : Finset (ProbabilityMeasure H)) := by
  classical
  let F := frozenFamilyOfExactSpec M spec m h41 hinv
  rw [exactGR_iff_common_reachable_target M spec m h41 hinv hmode]
  constructor
  · intro hcommon
    apply Finset.ext
    intro ν
    constructor
    · intro hν
      obtain ⟨i, hi, hiν⟩ := Finset.mem_image.mp hν
      change ν ∈ ({spec.target} : Finset (ProbabilityMeasure H))
      rw [Finset.mem_singleton]
      exact hiν.symm.trans (hcommon i hi)
    · intro hν
      have htarget : ν = spec.target := Finset.mem_singleton.mp hν
      subst ν
      obtain ⟨i, hi⟩ := reachableRepresentatives_nonempty
        M.inducedKernel H F
      exact Finset.mem_image.mpr
        ⟨i, hi, hcommon i hi⟩
  · intro hsharp i hi
    have hmem :
        observedStationaryForClass M.inducedKernel
          spec.descriptor i ∈ sharpObservedFamily M.inducedKernel F :=
      Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [hsharp] at hmem
    exact Finset.mem_singleton.mp hmem

end SharpFamilyExactGRBridge
end MultipleLimit
end PermanssonResearch
