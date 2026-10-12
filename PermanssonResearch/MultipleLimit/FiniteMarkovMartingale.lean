import PermanssonResearch.MultipleLimit.FiniteMarkovConditionalEvent
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Tactic

/-!
# C53-02 — true centered canonical finite-Markov martingale

The natural filtration, exact next-event conditional probability, and
bounded centered innovations are built in preceding research modules.
This file promotes those identities into a genuine mathlib Martingale,
with no independence, stationarity or aperiodicity premise.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovMartingale

open FiniteCanonicalPath
open FiniteMarkovCentered
open FiniteMarkovConditionalEvent
open FiniteMarkovMartingaleStep
open FiniteKernelRealBridge
open FiniteOccupationTelescoping

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [StandardBorelSpace Y]
variable [Nonempty Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- Both the next-state indicator and its predictable kernel row
probability are integrable on the actual canonical infinite path law. -/
private theorem predictable_integrable
    (μ : ProbabilityMeasure Y) (z : Y) (t : ℕ) :
    Integrable (fun w : ℕ → Y => realTransition K (w t) z)
      (canonicalPathLaw K μ.toMeasure) := by
  let P := canonicalPathLaw K μ.toMeasure
  have hcoord : Measurable (fun w : ℕ → Y => w t) :=
    measurable_pi_apply t
  have hf : Measurable (fun w : ℕ → Y => realTransition K (w t) z) :=
    (measurable_of_finite (fun y : Y => realTransition K y z)).comp hcoord
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact ae_of_all _ (fun w => by
    rw [Real.norm_eq_abs, abs_of_nonneg (realTransition_nonneg K (w t) z)]
    exact realTransition_le_one K (w t) z)

/-- The fixed next-state indicator is integrable and exactly agrees
with the event indicator used by the conditional-probability theorem. -/
private theorem next_indicator_integrable
    (μ : ProbabilityMeasure Y) (z : Y) (t : ℕ) :
    Integrable (fun w : ℕ → Y => indicatorAt w z (t+1))
      (canonicalPathLaw K μ.toMeasure) := by
  have hm : Measurable (fun w : ℕ → Y => indicatorAt w z (t+1)) := by
    unfold indicatorAt
    exact Measurable.ite
      (measurableSet_eq_fun (measurable_pi_apply (t+1)) measurable_const)
      measurable_const measurable_const
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ (fun w => by
    rw [Real.norm_eq_abs, abs_of_nonneg (indicatorAt_nonneg w z (t+1))]
    exact indicatorAt_le_one w z (t+1))

/-- Exactly centered canonical innovation, conditional on the whole
sigma algebra of observations up to time t. -/
theorem centered_increment_condExp_zero
    (μ : ProbabilityMeasure Y) (z : Y) (t : ℕ) :
    condExp (pastFiltration (Y := Y) t)
      (canonicalPathLaw K μ.toMeasure) (increment K z t)
        =ᵐ[canonicalPathLaw K μ.toMeasure]
          (fun _ : ℕ → Y => (0 : ℝ)) := by
  let P := canonicalPathLaw K μ.toMeasure
  let ℱ := pastFiltration (Y := Y)
  have hnext := canonical_next_singleton_conditional_probability K μ t z
  have hevent :
      ({w : ℕ → Y | w (t+1) = z} : Set (ℕ → Y)).indicator
        (fun _ : ℕ → Y => (1 : ℝ)) =
      (fun w : ℕ → Y => indicatorAt w z (t+1)) := by
    funext w
    by_cases h : w (t+1) = z <;> simp [indicatorAt, h]
  change P[({w : ℕ → Y | w (t+1) = z} : Set (ℕ → Y)).indicator
        (fun _ : ℕ → Y => (1 : ℝ)) | ℱ t] =ᵐ[P]
      (fun w : ℕ → Y => realTransition K (w t) z) at hnext
  rw [hevent] at hnext
  have hpred :
      StronglyMeasurable[ℱ t]
        (fun w : ℕ → Y => realTransition K (w t) z) := by
    have hcoord : Measurable[ℱ t] (fun w : ℕ → Y => w t) :=
      coordinate_measurable_at (Y := Y) t t le_rfl
    exact ((measurable_of_finite
      (fun y : Y => realTransition K y z)).comp hcoord).stronglyMeasurable
  have hcond :
      P[(fun w : ℕ → Y => realTransition K (w t) z) | ℱ t] =
        (fun w : ℕ → Y => realTransition K (w t) z) :=
    condExp_of_stronglyMeasurable (ℱ.le t)
      hpred (predictable_integrable K μ z t)
  change P[(fun w : ℕ → Y =>
      indicatorAt w z (t+1) - realTransition K (w t) z) | ℱ t] =ᵐ[P]
        (fun _ : ℕ → Y => (0 : ℝ))
  rw [condExp_sub (next_indicator_integrable K μ z t)
    (predictable_integrable K μ z t) (ℱ t), hcond]
  filter_upwards [hnext] with w hw
  simp [hw]

/-- The centered cumulative innovations are an actual martingale, not
a surrogate claim about transition matrix rows. -/
theorem canonical_centered_martingale
    (μ : ProbabilityMeasure Y) (z : Y) :
    Martingale (partialSum K z) (pastFiltration (Y := Y))
      (canonicalPathLaw K μ.toMeasure) := by
  apply martingale_of_condExp_sub_eq_zero_nat
    (partialSum_stronglyAdapted K z)
    (partialSum_integrable K μ z)
  intro t
  have h := centered_increment_condExp_zero K μ z t
  have hd :
      (fun w : ℕ → Y =>
        partialSum K z (t+1) w - partialSum K z t w) =
        increment K z t := by
    funext w
    rw [partialSum_succ]
    ring
  simpa only [Pi.sub_apply, partialSum_succ, add_sub_cancel_left] using h

end FiniteMarkovMartingale
end MultipleLimit
end PermanssonResearch
