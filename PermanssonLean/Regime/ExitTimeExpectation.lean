import PermanssonLean.Regime.SurvivalBridge
import Mathlib.Basic.Real.ENatENNReal
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH

variable {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

namespace RegimeSpecification

/-- Extended-natural tail count, expressed in ENNReal. -/
theorem enat_toENNReal_eq_tsum_lt (m : ℕ∞) :
    (m : ℝ≥0∞) =
      ∑' n : ℕ, if (n : ℕ∞) < m then (1 : ℝ≥0∞) else 0 := by
  cases m using ENat.recTopCoe with
  | top =>
      simp [ENNReal.tsum_const_eq_top_of_ne_zero]
  | coe k =>
      rw [ENat.toENNReal_coe]
      rw [tsum_eq_sum (s := Finset.range k)]
      · calc
          (k : ℝ≥0∞) =
              ∑ _n ∈ Finset.range k, (1 : ℝ≥0∞) := by simp
          _ = ∑ n ∈ Finset.range k,
              if (n : ℕ∞) < (k : ℕ∞) then (1 : ℝ≥0∞) else 0 := by
                apply Finset.sum_congr rfl
                intro n hn
                have hnk : n < k := Finset.mem_range.mp hn
                simp [ENat.natCast_lt_natCast, hnk]
      · intro n hn
        simp only [Finset.mem_range, not_lt] at hn
        simp [not_lt.mpr hn]

/-- Indicator for the event that the exit time exceeds n. -/
noncomputable def exitTailIndicator
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ)
    (w : ℕ → JointState S X) : ℝ≥0∞ :=
  if (n : ℕ∞) < exitTime spec w then 1 else 0

theorem exitTailIndicator_eq_setIndicator
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    exitTailIndicator spec n =
      (survivesThroughSet spec n).indicator
        (fun _ : ℕ → JointState S X => (1 : ℝ≥0∞)) := by
  funext w
  by_cases hs : SurvivesThrough spec n w
  · have hlt : (n : ℕ∞) < exitTime spec w :=
      (exitTime_gt_nat_iff spec w n).2 hs
    simp [exitTailIndicator, Set.indicator, survivesThroughSet, hs, hlt]
  · have hnotlt : ¬ (n : ℕ∞) < exitTime spec w := by
      intro hlt
      exact hs ((exitTime_gt_nat_iff spec w n).1 hlt)
    simp [exitTailIndicator, Set.indicator, survivesThroughSet, hs, hnotlt]

theorem measurable_exitTailIndicator
    (spec : RegimeSpecification (JointState S X) H)
    (n : ℕ) :
    Measurable (exitTailIndicator spec n) := by
  rw [exitTailIndicator_eq_setIndicator]
  exact measurable_const.indicator (measurableSet_survivesThroughSet spec n)

/-- ENNReal-valued exit time. -/
noncomputable def exitTimeENNReal
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) : ℝ≥0∞ :=
  (exitTime spec w : ℝ≥0∞)

theorem exitTimeENNReal_eq_tsum
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) :
    exitTimeENNReal spec w =
      ∑' n : ℕ, exitTailIndicator spec n w := by
  rw [exitTimeENNReal, enat_toENNReal_eq_tsum_lt]
  rfl

theorem measurable_exitTimeENNReal
    (spec : RegimeSpecification (JointState S X) H) :
    Measurable (exitTimeENNReal spec) := by
  rw [show exitTimeENNReal spec =
      fun w => ∑' n : ℕ, exitTailIndicator spec n w by
        funext w
        exact exitTimeENNReal_eq_tsum spec w]
  exact Measurable.ennreal_tsum fun n => measurable_exitTailIndicator spec n

/-- Extended expected first-exit time; it may equal +∞. -/
noncomputable def expectedExitTime
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) : ℝ≥0∞ :=
  ∫⁻ w, exitTimeENNReal spec w ∂M.pathLaw (Measure.dirac y)

/-- Tail-sum formula for the first-exit time. -/
theorem expectedExitTime_eq_tsum_survivalProbability
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X) :
    expectedExitTime M spec y =
      ∑' n : ℕ, survivalProbability M spec y n := by
  unfold expectedExitTime
  simp_rw [exitTimeENNReal_eq_tsum]
  rw [lintegral_tsum]
  · congr with n
    rw [exitTailIndicator_eq_setIndicator]
    rw [lintegral_indicator_const
      (measurableSet_survivesThroughSet spec n)]
    simp [survivalProbability]
  · intro n
    exact (measurable_exitTailIndicator spec n).aemeasurable

/-- Theorem 4.2a, equation (11c): the extended expected first-exit time is
the Green / tail series of killed-kernel survival masses. Divergence to +∞
is allowed. -/
theorem expectedExitTime_eq_greenSeries
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {y : JointState S X}
    (hy : y ∈ spec.region) :
    expectedExitTime M spec y =
      ∑' n : ℕ, killedSurvivalMass M spec n y := by
  rw [expectedExitTime_eq_tsum_survivalProbability]
  congr with n
  exact survivalProbability_eq_killedSurvivalMass M spec n hy

end RegimeSpecification

end PermanssonLean
