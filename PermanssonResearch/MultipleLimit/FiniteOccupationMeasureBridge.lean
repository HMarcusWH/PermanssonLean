import PermanssonResearch.MultipleLimit.FiniteOccupationStrongLaw
import PermanssonResearch.MultipleLimit.FiniteStateOccupation
import PermanssonResearch.MultipleLimit.FiniteUniformAverage
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# C53-06 — actual physical empirical probability weak convergence

Finite empirical vectors and the frozen positive-horizon empirical
ProbabilityMeasure share exactly the same point masses. Finite discrete
weak convergence is therefore reduced to the already proved coordinatewise
a.s. Markov-chain occupation theorem, tested against ALL bounded continuous
real functions, not just a chosen observable.

This module bridges the original probability-measure semantics without
changing the frozen v0.1.8 regime specification or any state normalization.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteOccupationMeasureBridge

open FiniteStateOccupation
open FiniteUniformAverage
open FiniteOccupationVector
open FiniteOccupationTelescoping
open FiniteOccupationStrongLaw
open FiniteKernelInvariantUniqueness
open FiniteKernelRealBridge
open CanonicalClassSelector
open ClassStationarySelectionLaw
open KernelCommunication

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [Nonempty Y] [DecidableEq Y]

/-- Genuine integral over the frozen physical occupation law is the
time-zero-inclusive arithmetic average at exactly the declared horizon. -/
theorem empiricalOccupation_integral_eq_average
    (w : ℕ → Y) (T : ℕ) (hT : 0 < T) (f : Y → ℝ) :
    (∫ y, f y ∂(empiricalOccupation w T hT).toMeasure) =
      ((T : ℝ)⁻¹) * ∑ t ∈ Finset.range T, f (w t) := by
  have hmeasure :
      (empiricalOccupation w T hT).toMeasure =
        Measure.map (fun i : Fin T => w (i : ℕ))
          (PermanssonLean.RegimeSpecification.uniformFinProbability T hT).toMeasure := rfl
  rw [hmeasure]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [FiniteUniformAverage.integral_uniformFin_eq_average T hT]
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => f (w i))]

/-- Exact singleton mass of a genuine positive-horizon physical
occupation ProbabilityMeasure equals the real empirical vector coordinate. -/
theorem empiricalOccupation_singleton_real
    (w : ℕ → Y) (n : ℕ) (j : Y) :
    (empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure.real {j} =
      empiricalVector w n j := by
  have hm : MeasurableSet ({j} : Set Y) := measurableSet_singleton j
  calc
    (empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure.real {j} =
        ∫ y : Y, ({j} : Set Y).indicator
          (fun _ : Y => (1 : ℝ)) y
          ∂(empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure :=
      (integral_indicator_one hm).symm
    _ = (((n+1 : ℕ) : ℝ)⁻¹) *
        (∑ t ∈ Finset.range (n+1), indicatorAt w j t) := by
      rw [empiricalOccupation_integral_eq_average]
      congr 1
      apply Finset.sum_congr rfl
      intro t ht
      by_cases h : w t = j <;> simp [indicatorAt, Set.indicator, h]
    _ = empiricalVector w n j := rfl

/-- Finite discrete physical weak topology is controlled by every
point mass, not solely by the stationary barycenter. -/
theorem physical_weak_limit_of_vector
    [TopologicalSpace Y] [DiscreteTopology Y]
    [OpensMeasurableSpace Y]
    (w : ℕ → Y) (π : ProbabilityMeasure Y)
    (hvector : Tendsto (fun n : ℕ => empiricalVector w n)
      atTop (𝓝 (realPointMass π))) :
    Tendsto
      (fun n : ℕ =>
        empiricalOccupation w (n+1) (Nat.succ_pos n))
      atTop (𝓝 π) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hcoord (j : Y) :
      Tendsto (fun n : ℕ => empiricalVector w n j)
        atTop (𝓝 (realPointMass π j)) :=
    (tendsto_pi_nhds.mp hvector) j
  have hsum :
      Tendsto (fun n : ℕ =>
        ∑ j : Y, empiricalVector w n j * f j)
        atTop (𝓝 (∑ j : Y, realPointMass π j * f j)) :=
    tendsto_finsetSum _ (fun j hj =>
      (hcoord j).mul_const (f j))
  have hident (n : ℕ) :
      (∫ j, f j ∂(empiricalOccupation w (n+1)
        (Nat.succ_pos n)).toMeasure) =
      ∑ j : Y, empiricalVector w n j * f j := by
    rw [integral_fintype (Integrable.of_finite)]
    simp_rw [empiricalOccupation_singleton_real w n]
    simp only [smul_eq_mul]
  have htarget :
      (∫ j, f j ∂π.toMeasure) =
        ∑ j : Y, realPointMass π j * f j := by
    rw [integral_fintype (Integrable.of_finite)]
    simp only [realPointMass, smul_eq_mul]
  simpa only [hident, htarget] using hsum

/-- THE whole weak-measure occupation statement for the actual infinite
canonical Markov path law, allowing periodic or nonirreducible chains. -/
theorem canonical_physical_occupation_ae_limit
    [TopologicalSpace Y] [DiscreteTopology Y]
    [OpensMeasurableSpace Y] [StandardBorelSpace Y]
    (K : Kernel Y Y) [IsMarkovKernel K]
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂FiniteCanonicalPath.canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n : ℕ =>
        empiricalOccupation w (n+1) (Nat.succ_pos n))
        atTop (𝓝 (stationaryForSet K
          (CommunicatingClass K
            (selectedRepresentative K w)))) := by
  filter_upwards [canonical_empirical_vector_ae_limit K μ] with w hw
  exact physical_weak_limit_of_vector w _ hw

end FiniteOccupationMeasureBridge
end MultipleLimit
end PermanssonResearch
