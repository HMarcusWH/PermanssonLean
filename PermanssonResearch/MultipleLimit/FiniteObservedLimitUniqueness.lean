import PermanssonResearch.MultipleLimit.FiniteExactGRRecovery
import PermanssonResearch.MultipleLimit.FiniteOccupationRandomLaw
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic

/-!
# C54-01 — uniqueness of the original and random observed occupation limits

The original v0.1.8 Exact GR certificate and the C2 random occupation
theorem control the SAME empirical probability-measure sequence under the
SAME infinite canonical strategic-world path law. Under a Hausdorff
probability-measure topology, both limits must agree almost surely.

This module neither postulates occupation convergence nor conflates the
random limit with its barycenter. The original convergence mode must be
literally almostSureWeak, rather than an arbitrary custom predicate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteObservedLimitUniqueness

open PermanssonLean
open PermanssonLean.RegimeSpecification
open FiniteCanonicalPath
open FiniteOccupationRandomLaw
open FiniteStateOccupation
open FiniteExactGRRecovery

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

/-- Every originally admissible initial law has an a.s. C2 observed
random occupation limit equal to the original exact-regime target.
Uniqueness is used only after identifying the *same* pathwise sequence. -/
theorem exactGR_observedOccupationLimit_ae
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (m : Measure (JointState S X))
    (hExact : IsExactGeneratedRegime M spec m)
    (hmode : spec.convergenceMode =
      ConvergenceMode.almostSureWeak (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (hμ : IsAdmissibleInitialLaw spec μ) :
    ∀ᵐ w ∂canonicalPathLaw M.inducedKernel μ.toMeasure,
      observedOccupationLimit M.inducedKernel spec.descriptor w =
        spec.target := by
  have hOriginal := exactGR_limitingOccupation M spec m hExact μ hμ
  unfold IsLimitingOccupationLaw at hOriginal
  rw [hmode] at hOriginal
  change ∀ᵐ w ∂M.pathLaw μ.toMeasure,
    Tendsto
      (fun n : ℕ => RegimeSpecification.empiricalOccupation
        spec w (n+1) (Nat.succ_pos n))
      atTop (𝓝 spec.target) at hOriginal
  rw [typed_pathLaw_eq_canonical M μ.toMeasure] at hOriginal
  have hC2 :=
    observedOccupationLimit_ae_correct M.inducedKernel μ spec.descriptor
  filter_upwards [hOriginal, hC2] with w hOld hNew
  have hSame :
      (fun n : ℕ => RegimeSpecification.empiricalOccupation
        spec w (n+1) (Nat.succ_pos n)) =
      (fun n : ℕ =>
        (FiniteStateOccupation.empiricalOccupation w
          (n+1) (Nat.succ_pos n)).map spec.descriptor) := by
    funext n
    exact original_empirical_eq_physical_map spec w (n+1) (Nat.succ_pos n)
  rw [hSame] at hOld
  exact tendsto_nhds_unique hNew hOld

end FiniteObservedLimitUniqueness
end MultipleLimit
end PermanssonResearch
