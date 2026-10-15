import PermanssonResearch.RegimeExit.ExitConservation
import Mathlib.Tactic

/-!
# C-Exit — genuine point/law agreement for Dirac initial distributions

The law-started routing measure has the same physical kernel iteration and
the same canonical path event as point-started routing.  This bridge proves
measure EQUALITY, not merely agreement on a chosen destination or a numerical
test set.  The initial point is required to belong to the frozen B.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

private theorem dirac_initial_supported
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region) :
    (diracProba y).toMeasure spec.region = 1 := by
  change (Measure.dirac y) spec.region = 1
  rw [Measure.dirac_apply' _ spec.region_measurable]
  simp [hy]

/-- Single-step routing agrees as genuine measures for a Dirac initial law. -/
theorem firstExitStepMeasureFromLaw_dirac
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region) :
    firstExitStepMeasureFromLaw M spec (diracProba y) n =
      firstExitStepMeasure M spec n y := by
  ext D hD
  have hLaw := firstExitStepFromLaw_eq_pathEvent M spec (diracProba y)
    (dirac_initial_supported spec hy) n D hD
  have hPoint := firstExitStep_eq_pathEvent M spec n hy D hD
  change M.pathLaw (Measure.dirac y) (firstExitAtDestination spec n D) =
    firstExitStepMeasureFromLaw M spec (diracProba y) n D at hLaw
  change M.pathLaw (Measure.dirac y) (firstExitAtDestination spec n D) =
    firstExitStepMeasure M spec n y D at hPoint
  exact hLaw.symm.trans hPoint

/-- The entire finite routing measure is identical in both constructors. -/
theorem exitRoutingFiniteMeasureFromLaw_dirac
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) {y : JointState S X} (hy : y ∈ spec.region) :
    exitRoutingFiniteMeasureFromLaw M spec (diracProba y) L =
      exitRoutingFiniteMeasure M spec y L := by
  induction L with
  | zero => rfl
  | succ L ih =>
      change exitRoutingFiniteMeasureFromLaw M spec (diracProba y) L +
        firstExitStepMeasureFromLaw M spec (diracProba y) L =
          exitRoutingFiniteMeasure M spec y L +
            firstExitStepMeasure M spec L y
      rw [ih, firstExitStepMeasureFromLaw_dirac M spec L hy]

/-- The infinite countable measure sums also agree exactly, not via limits
of rational approximations. -/
theorem exitRoutingInfiniteMeasureFromLaw_dirac
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region) :
    exitRoutingInfiniteMeasureFromLaw M spec (diracProba y) =
      exitRoutingInfiniteMeasure M spec y := by
  unfold exitRoutingInfiniteMeasureFromLaw exitRoutingInfiniteMeasure
  congr 1
  funext n
  exact firstExitStepMeasureFromLaw_dirac M spec n hy

theorem exitRoutingFiniteFromLaw_dirac
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (L : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) :
    exitRoutingFiniteFromLaw M spec L (diracProba y) D =
      exitRoutingFinite M spec L y D := by
  exact congrArg (fun ν : Measure (JointState S X) => ν D)
    (exitRoutingFiniteMeasureFromLaw_dirac M spec L hy)

theorem exitRoutingInfiniteFromLaw_dirac
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) :
    exitRoutingInfiniteFromLaw M spec (diracProba y) D =
      exitRoutingInfinite M spec y D := by
  exact congrArg (fun ν : Measure (JointState S X) => ν D)
    (exitRoutingInfiniteMeasureFromLaw_dirac M spec hy)

/-- The already frozen point-start survival event is preserved verbatim. -/
theorem survivalForeverProbabilityFromLaw_dirac
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) :
    survivalForeverProbabilityFromLaw M spec (diracProba y) =
      survivalForeverProbability M spec y := rfl

end PermanssonResearch.RegimeExit
