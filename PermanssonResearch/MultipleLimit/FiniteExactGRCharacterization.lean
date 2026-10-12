import PermanssonResearch.MultipleLimit.FiniteClassTargetNecessity
import Mathlib.Tactic

/-!
# C54-03 — finite-state Exact GR if and only if common reachable target

Unlike the C2 sufficient certificate, this theorem characterizes the
ORIGINAL frozen v0.1.8 IsExactGeneratedRegime, under its existing
Assumption 4.1, exact region invariance and almostSureWeak mode.

The converse uses C54-01/02 and uniqueness of weak measure-valued
limits; the sufficient direction reuses the proved C2 theorem.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteExactGRCharacterization

open PermanssonLean
open PermanssonLean.RegimeSpecification
open BasinFamily
open ClassDescriptorSelectionLaw
open FiniteExactGRRecovery
open FiniteClassTargetNecessity

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

/-- The C3 headline: the ORIGINAL exact generated-regime predicate is
equivalent to equality between its frozen target and each observed
stationary law of a class selected with nonzero probability from the
frozen basin. Inaccessible classes cannot obstruct Exact GR. -/
theorem exactGR_iff_common_reachable_target
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h41 : Assumption41 M spec m)
    (hinv : IsExactlyInvariant M spec)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H) :
    IsExactGeneratedRegime M spec m ↔
      ∀ i ∈ reachableRepresentatives M.inducedKernel H
        (frozenFamilyOfExactSpec M spec m h41 hinv),
        observedStationaryForClass M.inducedKernel spec.descriptor i =
          spec.target := by
  constructor
  · intro hExact
    exact exactGR_common_target_on_reachable
      M spec m h41 hinv hExact hmode
  · intro hcommon
    exact recover_original_exactGR_of_common_class_target
      M spec m h41 hinv hmode hcommon

/-- Equivalent closed characterization with the original Assumption
4.1 and exact-invariance gates existentially visible, not silently
removed or weakened. -/
theorem exactGR_iff_exists_gates_common_reachable_target
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H) :
    IsExactGeneratedRegime M spec m ↔
      ∃ (h41 : Assumption41 M spec m)
        (hinv : IsExactlyInvariant M spec),
        ∀ i ∈ reachableRepresentatives M.inducedKernel H
          (frozenFamilyOfExactSpec M spec m h41 hinv),
          observedStationaryForClass M.inducedKernel spec.descriptor i =
            spec.target := by
  constructor
  · intro hExact
    let h41 := exactGR_assumption41 M spec m hExact
    let hinv := exactGR_exactlyInvariant M spec m hExact
    refine ⟨h41, hinv, ?_⟩
    exact (exactGR_iff_common_reachable_target
      M spec m h41 hinv hmode).mp hExact
  · rintro ⟨h41, hinv, hcommon⟩
    exact (exactGR_iff_common_reachable_target
      M spec m h41 hinv hmode).mpr hcommon

end FiniteExactGRCharacterization
end MultipleLimit
end PermanssonResearch
