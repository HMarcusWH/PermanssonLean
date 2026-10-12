import PermanssonResearch.MultipleLimit.FiniteExactGRCharacterization
import Mathlib.Tactic

/-!
# C54-04 — finite Exact GR obstruction and target independence

One basin-reachable class whose observed law differs from the frozen
target obstructs the ORIGINAL Exact GR predicate. Two reachable classes
with distinct observed laws obstruct EVERY single prescribed target,
including after replacing the target field of the frozen specification.

Replacing a target cannot change the original basin/region/descriptor,
the Assumption 4.1 obligations, exact invariance or convergence mode.
All such transport steps are explicit rather than postulated.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteExactGRObstruction

open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteExactGRRecovery
open FiniteClassTargetNecessity
open FiniteExactGRCharacterization
open BasinFamily
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

/-- Target-only modification: all the original frozen structural
fields and their proof obligations remain unchanged. -/
def withTarget
    (spec : RegimeSpecification (JointState S X) H)
    (ν : ProbabilityMeasure H) :
    RegimeSpecification (JointState S X) H :=
  { spec with target := ν }

theorem withTarget_assumption41
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (ν : ProbabilityMeasure H) :
    Assumption41 M (withTarget spec ν) m ↔
      Assumption41 M spec m := Iff.rfl

theorem withTarget_invariance
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (ν : ProbabilityMeasure H) :
    IsExactlyInvariant M (withTarget spec ν) ↔
      IsExactlyInvariant M spec := Iff.rfl

theorem withTarget_mode
    (spec : RegimeSpecification (JointState S X) H)
    (ν : ProbabilityMeasure H) :
    (withTarget spec ν).convergenceMode =
      spec.convergenceMode := rfl

/-- A target replacement does not enlarge or shrink the actual
basin-reachable recurrent-class family. -/
theorem withTarget_reachable_family_eq
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (ν : ProbabilityMeasure H)
    (h41 : Assumption41 M spec m)
    (hinv : IsExactlyInvariant M spec) :
    reachableRepresentatives M.inducedKernel H
      (frozenFamilyOfExactSpec M (withTarget spec ν) m
        ((withTarget_assumption41 M spec m ν).mpr h41)
        ((withTarget_invariance M spec ν).mpr hinv)) =
    reachableRepresentatives M.inducedKernel H
      (frozenFamilyOfExactSpec M spec m h41 hinv) := by
  apply reachableRepresentatives_eq_of_basin_eq
  rfl

/-- Any basin-reachable observed class with a different target rules
out the *original* frozen single-target Exact GR predicate. -/
theorem not_exactGR_of_reachable_target_mismatch
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h41 : Assumption41 M spec m)
    (hinv : IsExactlyInvariant M spec)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H)
    (i : JointState S X)
    (hi : i ∈ reachableRepresentatives M.inducedKernel H
      (frozenFamilyOfExactSpec M spec m h41 hinv))
    (hneq : observedStationaryForClass
      M.inducedKernel spec.descriptor i ≠ spec.target) :
    ¬ IsExactGeneratedRegime M spec m := by
  intro hExact
  exact hneq ((exactGR_iff_common_reachable_target
    M spec m h41 hinv hmode).mp hExact i hi)

/-- A nonempty actually reachable class family has at most one
deterministic class-common descriptor target. This is independent of
effective computation of the target. -/
theorem common_reachable_target_unique
    {Y H' : Type*} [MeasurableSpace Y] [Fintype Y]
    [MeasurableSingletonClass Y] [Nonempty Y]
    [MeasurableSpace H']
    (K : Kernel Y Y) [IsMarkovKernel K]
    (F : FrozenBasinFamily K H')
    (ν ξ : ProbabilityMeasure H')
    (hν : ∀ i ∈ reachableRepresentatives K H' F,
      observedStationaryForClass K F.descriptor i = ν)
    (hξ : ∀ i ∈ reachableRepresentatives K H' F,
      observedStationaryForClass K F.descriptor i = ξ) :
    ν = ξ := by
  obtain ⟨i, hi⟩ := reachableRepresentatives_nonempty K H' F
  exact (hν i hi).symm.trans (hξ i hi)

/-- Two genuinely basin-reachable and observably distinct recurrent
classes prevent ALL possible single frozen targets under the original
almost-sure-weak convergence mode. No uniform positive weight is
assumed; arbitrary positive class-selection probability suffices. -/
theorem no_exactGR_for_any_target_of_incompatible_classes
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (h41 : Assumption41 M spec m)
    (hinv : IsExactlyInvariant M spec)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H)
    (i j : JointState S X)
    (hi : i ∈ reachableRepresentatives M.inducedKernel H
      (frozenFamilyOfExactSpec M spec m h41 hinv))
    (hj : j ∈ reachableRepresentatives M.inducedKernel H
      (frozenFamilyOfExactSpec M spec m h41 hinv))
    (hneq : observedStationaryForClass
        M.inducedKernel spec.descriptor i ≠
      observedStationaryForClass M.inducedKernel spec.descriptor j) :
    ∀ ν : ProbabilityMeasure H,
      ¬ IsExactGeneratedRegime M (withTarget spec ν) m := by
  intro ν hExact
  have h41ν : Assumption41 M (withTarget spec ν) m :=
    (withTarget_assumption41 M spec m ν).mpr h41
  have hinvν : IsExactlyInvariant M (withTarget spec ν) :=
    (withTarget_invariance M spec ν).mpr hinv
  have hmodeν : (withTarget spec ν).convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H := by
    rw [withTarget_mode]
    exact hmode
  have hfamily := withTarget_reachable_family_eq
    M spec m ν h41 hinv
  have hcommon := (exactGR_iff_common_reachable_target
    M (withTarget spec ν) m h41ν hinvν hmodeν).mp hExact
  have hiν : i ∈ reachableRepresentatives M.inducedKernel H
      (frozenFamilyOfExactSpec M (withTarget spec ν) m h41ν hinvν) := by
    rw [hfamily]
    exact hi
  have hjν : j ∈ reachableRepresentatives M.inducedKernel H
      (frozenFamilyOfExactSpec M (withTarget spec ν) m h41ν hinvν) := by
    rw [hfamily]
    exact hj
  have hI := hcommon i hiν
  have hJ := hcommon j hjν
  change observedStationaryForClass M.inducedKernel spec.descriptor i =
    ν at hI
  change observedStationaryForClass M.inducedKernel spec.descriptor j =
    ν at hJ
  exact hneq (hI.trans hJ.symm)

end FiniteExactGRObstruction
end MultipleLimit
end PermanssonResearch
