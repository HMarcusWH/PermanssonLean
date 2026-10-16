import PermanssonResearch.RegimeExit.StopHistoryFuture
import PermanssonResearch.RegimeExit.ExitRouting
import Mathlib.Tactic

/-!
# C-Exit C — genuine subprobability measure on first-exit future paths

All measures here are on the ORIGINAL infinite-path space, not an
artificial post-exit model. The first-exit restriction may have mass
strictly below one. There is NO normalization when exit mass is zero.
The endpoint-only Markov-kernel restart identity remains a separate
unproved obligation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X]
variable [MeasurableSpace A] [MeasurableSpace H]

/-- Actual conditional-event SUBMEASURE on infinite futures, where
the initial observation of the future occurs at n+1 (first exit).
Never evaluates at an infinite exit time. -/
noncomputable def finiteStoppedFutureMeasure
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X)
    (D : Set (JointState S X)) :
    Measure (ℕ → JointState S X) :=
  ((N.pathLaw (Measure.dirac y)).restrict
    (firstExitAtDestination spec n D)).map
      (pathTailShift (S := S) (X := X) (n+1))

/-- Every measurable full-future event is evaluated against the
correct shifted, restricted ORIGINAL path law. -/
theorem finiteStoppedFutureMeasure_apply
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X)
    (D : Set (JointState S X))
    (F : Set (ℕ → JointState S X))
    (hF : MeasurableSet F) :
    finiteStoppedFutureMeasure N spec n y D F =
      N.pathLaw (Measure.dirac y)
        (firstExitAtDestination spec n D ∩
          (pathTailShift (S := S) (X := X) (n+1)) ⁻¹' F) := by
  unfold finiteStoppedFutureMeasure
  rw [Measure.map_apply (measurable_pathTailShift
      (S := S) (X := X) (n+1)) hF,
    Measure.restrict_apply (hF.preimage
      (measurable_pathTailShift (S := S) (X := X) (n+1)))]

/-- Genuine non-normalized mass: it is exactly PR66's nth exit
step mass, not one unless every path exits at this time. -/
theorem finiteStoppedFutureMeasure_univ
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    finiteStoppedFutureMeasure N spec n y D Set.univ =
      firstExitStepMass N spec n y D := by
  rw [finiteStoppedFutureMeasure_apply N spec n y D
    Set.univ MeasurableSet.univ]
  simpa using (firstExitStep_eq_pathEvent N spec n hy D hD)

/-- The full stopped-future law is identified with the legitimate
measure over first-exit histories, for ANY measurable future event. -/
theorem finiteStoppedFutureMeasure_eq_history
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X)
    (D : Set (JointState S X)) (hD : MeasurableSet D)
    (F : Set (ℕ → JointState S X)) (hF : MeasurableSet F) :
    finiteStoppedFutureMeasure N spec n y D F =
    ∫⁻ h in firstExitHistoryAt spec n D,
      (canonicalShiftedHistoryKernel N (n+1) h) F
      ∂((N.pathLaw (Measure.dirac y)).map
        (Preorder.frestrictLe (n+1))) := by
  rw [finiteStoppedFutureMeasure_apply N spec n y D F hF]
  exact firstExit_shifted_history_future_integral
    N spec n y D hD F hF

/-- Countable sum of real shifted-future submeasures, without any
artificial mass allocated to trajectories that never exit. -/
noncomputable def infiniteStoppedFutureMeasure
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) (D : Set (JointState S X)) :
    Measure (ℕ → JointState S X) :=
  Measure.sum fun n : ℕ =>
    finiteStoppedFutureMeasure N spec n y D

/-- The full infinite stopped-future path measure has EXACTLY the
original infinite first-exit routing mass. This is true even when
that mass is zero or strictly below one. -/
theorem infiniteStoppedFutureMeasure_univ
    (N : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region)
    (D : Set (JointState S X)) (hD : MeasurableSet D) :
    infiniteStoppedFutureMeasure N spec y D Set.univ =
      exitRoutingInfinite N spec y D := by
  calc
    infiniteStoppedFutureMeasure N spec y D Set.univ =
        ∑' n : ℕ,
          finiteStoppedFutureMeasure N spec n y D Set.univ := by
      exact Measure.sum_apply _ MeasurableSet.univ
    _ = ∑' n : ℕ, firstExitStepMass N spec n y D := by
      apply tsum_congr
      intro n
      exact finiteStoppedFutureMeasure_univ N spec n hy D hD
    _ = exitRoutingInfinite N spec y D := by
      exact (exitRoutingInfiniteMeasure_apply N spec y D hD).symm

end PermanssonResearch.RegimeExit
