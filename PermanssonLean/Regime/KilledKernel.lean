import PermanssonLean.Regime.Invariance
import Mathlib.Probability.Kernel.Composition.Comp

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

namespace RegimeSpecification

/-- The killed kernel associated with a regime region B.

Operationally this is the original induced Markov kernel with its output
measure restricted to B:
`K_B(y,C) = K(C ∩ B | y)`.

We deliberately keep the domain and codomain equal to the ambient state
space. Missing mass records trajectories that have already exited B.
-/
noncomputable def killedKernel
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) :
    Kernel (JointState S X) (JointState S X) :=
  M.inducedKernel.restrict spec.region_measurable

theorem killedKernel_apply
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) {C : Set (JointState S X)}
    (hC : MeasurableSet C) :
    killedKernel M spec y C =
      M.inducedKernel y (C ∩ spec.region) := by
  rw [killedKernel, Kernel.restrict_apply' _ spec.region_measurable _ hC]

theorem killedKernel_apply_region
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) :
    killedKernel M spec y spec.region =
      M.inducedKernel y spec.region := by
  rw [killedKernel_apply M spec y spec.region_measurable]
  simp

theorem killedKernel_apply_univ
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) :
    killedKernel M spec y Set.univ =
      M.inducedKernel y spec.region := by
  rw [killedKernel_apply M spec y MeasurableSet.univ]
  simp

instance killedKernel_isFinite
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) :
    IsFiniteKernel (killedKernel M spec) := by
  letI : IsMarkovKernel M.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov M
  unfold killedKernel
  infer_instance

instance killedKernel_isSFinite
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) :
    IsSFiniteKernel (killedKernel M spec) := by
  infer_instance

/-- A killed kernel is sub-probability-valued: total surviving mass is at most one. -/
theorem killedKernel_mass_le_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) :
    killedKernel M spec y Set.univ ≤ 1 := by
  rw [killedKernel_apply_univ M spec y]
  letI : IsMarkovKernel M.inducedKernel :=
    StrategicWorldModel.inducedKernel_isMarkov M
  exact prob_le_one

/-- Paper notation `(K_B^n 1_B)(y)`, represented setwise.

Because each killed transition already restricts its output to B, evaluating
the n-step killed kernel on B is the exact surviving mass after n steps.
-/
noncomputable def killedSurvivalMass
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X) : ℝ≥0∞ :=
  ((killedKernel M spec) ^ n) y spec.region

@[simp]
theorem killedSurvivalMass_zero
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X} (hy : y ∈ spec.region) :
    killedSurvivalMass M spec 0 y = 1 := by
  change (Measure.dirac y) spec.region = 1
  rw [Measure.dirac_apply' _ spec.region_measurable]
  simp [hy]

theorem killedSurvivalMass_one
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) :
    killedSurvivalMass M spec 1 y =
      M.inducedKernel y spec.region := by
  change killedKernel M spec y spec.region =
    M.inducedKernel y spec.region
  exact killedKernel_apply_region M spec y

theorem killedSurvivalMass_succ
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) (y : JointState S X) :
    killedSurvivalMass M spec (n + 1) y =
      ∫⁻ z, M.inducedKernel z spec.region
        ∂(((killedKernel M spec) ^ n) y) := by
  rw [killedSurvivalMass, Kernel.pow_succ_apply_eq_lintegral _ n y spec.region_measurable]
  congr with z
  exact killedKernel_apply_region M spec z

end RegimeSpecification

end PermanssonLean
