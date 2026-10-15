import PermanssonResearch.RegimeExit.ExitRouting
import PermanssonLean.Regime.QuasiStationary
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-!
# C-Exit — exact QSD destination routing under the original killed kernel

No all-state uniform persistence is inferred from an initial law. The case
theta=1 is a separate zero-exit statement, never a division by zero.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory Topology

namespace PermanssonResearch.RegimeExit
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uA uH
variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

/-- Genuine one-step QSD exit mass from the supplied probability law. -/
noncomputable def qsdOneStepExitMass
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (D : Set (JointState S X)) : ℝ≥0∞ :=
  (exitSubkernel M spec ∘ₘ μ.toMeasure) D

/-- Measured, not stipulated: killed^n μ = theta^n μ gives the first-exit law. -/
theorem qsd_firstExitStep_eq_pow_mul
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta)
    (n : ℕ) (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    firstExitStepMeasureFromLaw M spec μ n D =
      theta ^ n * qsdOneStepExitMass M spec μ D := by
  unfold firstExitStepMeasureFromLaw qsdOneStepExitMass
  rw [qsd_killedMeasureIterate_eq_smul M spec μ theta hQ n,
    Measure.comp_smul, Measure.smul_apply, smul_eq_mul]

/-- Exact finite geometric destination routing from QSD initial law. -/
theorem qsdRoutingFinite_eq_geometric
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta)
    (L : ℕ) (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    exitRoutingFiniteFromLaw M spec L μ D =
      (∑ n ∈ Finset.range L, theta ^ n) *
        qsdOneStepExitMass M spec μ D := by
  rw [exitRoutingFiniteFromLaw,
    exitRoutingFiniteMeasureFromLaw_apply M spec L μ D hD]
  simp_rw [qsd_firstExitStep_eq_pow_mul M spec μ theta hQ _ D hD]
  rw [Finset.sum_mul]

/-- The geometric fraction is a statement about the actual QSD law. -/
theorem qsdRoutingInfinite_eq_fraction
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta)
    (hθ : theta < 1)
    (D : Set (JointState S X))
    (hD : MeasurableSet D) :
    exitRoutingInfiniteFromLaw M spec μ D =
      qsdOneStepExitMass M spec μ D / (1 - theta) := by
  have hfinite : theta ≠ ∞ :=
    ne_of_lt (lt_trans hθ ENNReal.one_lt_top)
  have hpositive : (0 : ℝ≥0∞) < 1 - theta :=
    tsub_pos_iff_lt.mpr hθ
  rw [exitRoutingInfiniteFromLaw,
    exitRoutingInfiniteMeasureFromLaw_apply M spec μ D hD]
  simp_rw [qsd_firstExitStep_eq_pow_mul M spec μ theta hQ _ D hD]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  simp [div_eq_mul_inv, mul_comm]

/-- A certified QSD at theta=1 has *zero integrated exit mass*;
this says nothing about every other state inside B. -/
theorem qsdThetaOne_no_exit_of_conservation
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (hQ : IsQuasiStationaryDistribution M spec μ 1)
    (D : Set (JointState S X))
    (hD : MeasurableSet D)
    (hExitConservation :
      qsdOneStepExitMass M spec μ Set.univ +
        (killedKernel M spec ∘ₘ μ.toMeasure) Set.univ = 1) :
    qsdOneStepExitMass M spec μ D = 0 := by
  have hstay : (killedKernel M spec ∘ₘ μ.toMeasure) Set.univ = 1 := by
    rw [qsd_eigenmeasure M spec μ 1 hQ]
    simp
  have he : qsdOneStepExitMass M spec μ Set.univ = 0 := by
    rw [hstay] at hExitConservation
    have heq := ENNReal.eq_sub_of_add_eq ENNReal.one_ne_top hExitConservation
    simpa using heq
  have hle : qsdOneStepExitMass M spec μ D ≤
      qsdOneStepExitMass M spec μ Set.univ := measure_mono (Set.subset_univ D)
  exact le_antisymm (by simpa [he] using hle) bot_le

/-- Initial-law survival obeys QSD powers, not pointwise powers at every y. -/
theorem qsdSurvivalFinite_eq_pow
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (μ : ProbabilityMeasure (JointState S X))
    (theta : ℝ≥0∞)
    (hQ : IsQuasiStationaryDistribution M spec μ theta)
    (n : ℕ) :
    survivalProbabilityFromLaw M spec μ n = theta ^ n :=
  qsd_survivalProbability M spec μ theta hQ n

end PermanssonResearch.RegimeExit
