import PermanssonResearch.RegimeExit.ExitEvents
import PermanssonLean.Regime.Persistence
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Tactic

/-!
# C-Exit — actual sub-Markov exit and killed-composition measures

K is the original α→P→U induced Markov kernel. Both restrictions lose mass:
neither killedKernel nor exitSubkernel is asserted to be Markov.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.RegimeExit

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]
open PermanssonLean PermanssonLean.RegimeSpecification

/-- The actual world-transition exit subkernel, restricted on OUTPUT to Bᶜ. -/
noncomputable def exitSubkernel
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) :
    Kernel (JointState S X) (JointState S X) :=
  M.inducedKernel.restrict spec.region_measurable.compl

theorem exitSubkernel_apply
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) {D : Set (JointState S X)}
    (hD : MeasurableSet D) :
    exitSubkernel M spec y D =
      M.inducedKernel y (D \ spec.region) := by
  rw [exitSubkernel, Kernel.restrict_apply' _ spec.region_measurable.compl _ hD]
  rfl

theorem exitSubkernel_region_zero
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) :
    exitSubkernel M spec y spec.region = 0 := by
  rw [exitSubkernel_apply M spec y spec.region_measurable]
  simp

theorem exitSubkernel_mask
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) {D : Set (JointState S X)}
    (hD : MeasurableSet D) :
    exitSubkernel M spec y D =
      exitSubkernel M spec y (D \ spec.region) := by
  rw [exitSubkernel_apply M spec y hD]
  rw [exitSubkernel_apply M spec y (hD.diff spec.region_measurable)]
  simp [Set.diff_diff]

instance exitSubkernel_isFinite
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) :
    IsFiniteKernel (exitSubkernel M spec) := by
  letI : IsMarkovKernel M.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov M
  unfold exitSubkernel
  infer_instance

instance exitSubkernel_isSFinite
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) :
    IsSFiniteKernel (exitSubkernel M spec) := by
  infer_instance

/-- The normalized original K partitions its mass into inside and outside. -/
theorem exitSubkernel_mass_add_killedKernel_mass_eq_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) :
    exitSubkernel M spec y Set.univ +
      killedKernel M spec y Set.univ = 1 := by
  rw [exitSubkernel_apply M spec y MeasurableSet.univ,
    killedKernel_apply_univ M spec y]
  haveI : IsProbabilityMeasure (M.inducedKernel y) :=
    (StrategicWorldModel.inducedKernel_isMarkov M).isProbability y
  simpa using (measure_add_measure_compl spec.region_measurable (M.inducedKernel y)).symm

/-- The actual n-step killed measure, then one exit transition. -/
noncomputable def firstExitStepMeasure
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X) :
    Measure (JointState S X) :=
  exitSubkernel M spec ∘ₘ (((killedKernel M spec) ^ n) y)

/-- A scalar is only the evaluation of the genuine constructed measure. -/
noncomputable def firstExitStepMass
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X)
    (D : Set (JointState S X)) : ℝ≥0∞ :=
  firstExitStepMeasure M spec n y D

theorem firstExitStepMass_eq_lintegral
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X)
    (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    firstExitStepMass M spec n y D =
      ∫⁻ z, M.inducedKernel z (D \ spec.region)
        ∂(((killedKernel M spec) ^ n) y) := by
  unfold firstExitStepMass firstExitStepMeasure
  rw [Measure.bind_apply hD (Kernel.aemeasurable _)]
  congr 1
  funext z
  exact exitSubkernel_apply M spec z hD

/-- The time-zero first-exit measure is precisely one genuine exit row. -/
theorem firstExitStepMeasure_zero
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) :
    firstExitStepMeasure M spec 0 y = exitSubkernel M spec y := by
  simp [firstExitStepMeasure]

end PermanssonResearch.RegimeExit
