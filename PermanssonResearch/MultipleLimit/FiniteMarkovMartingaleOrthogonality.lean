import PermanssonResearch.MultipleLimit.FiniteMarkovMartingale
import PermanssonResearch.MultipleLimit.FiniteMarkovInterpolation
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Tactic

/-!
# C53-03 — canonical Markov innovation orthogonality

The genuine next-state centered increment has conditional mean zero
given the complete finite past. Mathlib's conditional expectation
pull-out theorem therefore makes it orthogonal to every bounded
past-measurable real observable, including any earlier innovation and
the entire partial centered sum. No independence or stationarity is
assumed, even for periodic/reducible chains.
-/

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteMarkovMartingaleOrthogonality

open FiniteCanonicalPath
open FiniteMarkovMartingaleStep
open FiniteMarkovMartingale
open FiniteMarkovInterpolation

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [StandardBorelSpace Y]
variable [Nonempty Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- Uniform orthogonality to every bounded observable of the genuine
past sigma algebra, proved via the certified martingale innovation. -/
theorem bounded_past_observable_cross_zero
    (μ : ProbabilityMeasure Y) (z : Y) (t : ℕ)
    (f : (ℕ → Y) → ℝ)
    (hf : StronglyMeasurable[pastFiltration (Y := Y) t] f)
    (C : ℝ) (hb : ∀ w, ‖f w‖ ≤ C) :
    (∫ w, f w * increment K z t w
      ∂canonicalPathLaw K μ.toMeasure) = 0 := by
  let P := canonicalPathLaw K μ.toMeasure
  let ℱ := pastFiltration (Y := Y)
  have hbound : ∀ᵐ w ∂P, ‖f w‖ ≤ C :=
    ae_of_all _ hb
  have hpull :
      P[(f * increment K z t) | ℱ t] =ᵐ[P]
        f * P[increment K z t | ℱ t] :=
    condExp_stronglyMeasurable_mul_of_bound (ℱ.le t)
      hf (increment_integrable K μ z t) C hbound
  have hcenter := centered_increment_condExp_zero K μ z t
  have hcondZero :
      P[(f * increment K z t) | ℱ t] =ᵐ[P]
        (fun _ : ℕ → Y => (0 : ℝ)) := by
    filter_upwards [hpull, hcenter] with w hw hz
    calc
      (P[(f * increment K z t) | ℱ t]) w =
          f w * (P[increment K z t | ℱ t]) w := hw
      _ = 0 := by rw [hz]; ring
  calc
    (∫ w, f w * increment K z t w ∂P) =
      ∫ w, (P[(f * increment K z t) | ℱ t]) w ∂P := by
        exact (integral_condExp (ℱ.le t)).symm
    _ = 0 := by
      rw [integral_congr_ae hcondZero]
      simp

/-- Distinct-time innovations are uncorrelated, even though the Markov
chain itself need not have independent successive states. -/
theorem increment_pairwise_orthogonal
    (μ : ProbabilityMeasure Y) (z : Y)
    {s t : ℕ} (hst : s < t) :
    (∫ w, increment K z s w * increment K z t w
      ∂canonicalPathLaw K μ.toMeasure) = 0 := by
  have hm : StronglyMeasurable[pastFiltration (Y := Y) t]
      (increment K z s) := by
    have hstep := increment_measurable_at K z s
    exact (hstep.mono
      ((pastFiltration (Y := Y)).mono (Nat.succ_le_of_lt hst))
      le_rfl).stronglyMeasurable
  apply bounded_past_observable_cross_zero K μ z t
    (increment K z s) hm 1
  intro w
  simpa only [Real.norm_eq_abs] using increment_bounded K z s w

/-- A genuine cumulative martingale's current partial sum is orthogonal
to the innovation occurring strictly after its recorded history. -/
theorem partialSum_next_increment_orthogonal
    (μ : ProbabilityMeasure Y) (z : Y) (t : ℕ) :
    (∫ w, partialSum K z t w * increment K z t w
      ∂canonicalPathLaw K μ.toMeasure) = 0 := by
  have hbound (w : ℕ → Y) :
      ‖partialSum K z t w‖ ≤ (t : ℝ) := by
    have h := partialSum_time_lipschitz K z w
      (s := 0) (t := t) (Nat.zero_le t)
    simpa [partialSum_zero, Real.norm_eq_abs] using h
  exact bounded_past_observable_cross_zero K μ z t
    (partialSum K z t) ((partialSum_stronglyAdapted K z) t)
    (t : ℝ) hbound

end FiniteMarkovMartingaleOrthogonality
end MultipleLimit
end PermanssonResearch
