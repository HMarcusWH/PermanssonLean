import PermanssonResearch.MultipleLimit.FiniteMarkovMartingaleSLLN
import PermanssonResearch.MultipleLimit.FiniteClassOccupation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# C53-05 — physical occupation strong law, without a residual hypothesis

The canonical Markov martingale strong law controls the actual empirical
stationarity defect using the exact finite-time telescoping bound.
Combined with recurrent-class residence and uniqueness of the class
invariant probability, this proves the entire finite empirical probability
VECTOR converges almost surely to the true stationary law of the
recurrent class selected by that same infinite path.

No stationarity of the initial law, aperiodicity, independent sample,
or presumed occupation limit is used.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteOccupationStrongLaw

open FiniteCanonicalPath
open KernelCommunication
open FiniteKernelRealBridge
open FiniteCesaroAlgebra
open FiniteKernelInvariantUniqueness
open FiniteMarkovMartingaleStep
open FiniteMarkovMartingaleSLLN
open FiniteOccupationVector
open FiniteOccupationTelescoping
open FiniteClassOccupation
open FiniteClassInvariantMeasure
open CanonicalClassSelector
open ClassStationarySelectionLaw

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y] [StandardBorelSpace Y]
variable [Nonempty Y] [DecidableEq Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

/-- The reciprocal of every positive occupation horizon vanishes. -/
private theorem inverse_succ_tendsto_zero :
    Tendsto (fun n : ℕ => (((n+1 : ℕ) : ℝ)⁻¹))
      atTop (𝓝 (0 : ℝ)) := by
  have hn : Tendsto (fun n : ℕ => n+1) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with n hnb
    omega
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.comp hn)

/-- The actual canonical empirical stationarity residual converges
coordinatewise to zero almost surely, for every finite Markov kernel. -/
theorem canonical_empirical_residual_ae_zero
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      ∀ z : Y,
        Tendsto
          (fun n : ℕ =>
            pushVector (realTransition K) (empiricalVector w n) z -
              empiricalVector w n z)
          atTop (𝓝 (0 : ℝ)) := by
  rw [ae_all_iff]
  intro z
  filter_upwards [canonical_partialSum_strong_law K μ z] with w hmart
  have hresidual :
      Tendsto (fun n : ℕ =>
        (((n+1 : ℕ) : ℝ)⁻¹) *
          transitionResidual (realTransition K) w z (n+1))
        atTop (𝓝 (0 : ℝ)) := by
    convert hmart using 1
    ext n
    rw [partialSum_eq_residual]
    ring
  have hbound :
      Tendsto (fun n : ℕ =>
        (pushVector (realTransition K) (empiricalVector w n) z -
          empiricalVector w n z) +
        (((n+1 : ℕ) : ℝ)⁻¹) *
          transitionResidual (realTransition K) w z (n+1))
        atTop (𝓝 (0 : ℝ)) := by
    have hAbs :
        Tendsto (fun n : ℕ =>
          |(pushVector (realTransition K) (empiricalVector w n) z -
            empiricalVector w n z) +
          (((n+1 : ℕ) : ℝ)⁻¹) *
            transitionResidual (realTransition K) w z (n+1)|)
          atTop (𝓝 (0 : ℝ)) := by
      apply squeeze_zero
      · intro n
        exact abs_nonneg _
      · intro n
        exact empiricalVector_stationarity_defect_bound
          (realTransition K) w n z
      · exact inverse_succ_tendsto_zero
    exact tendsto_zero_iff_norm_tendsto_zero.mpr
      (by simpa only [Real.norm_eq_abs] using hAbs)
  have hcancel := hbound.sub hresidual
  convert hcancel using 1
  · ext n
    ring
  · simp

/-- Lane C2's central unconditional finite-state almost-sure occupation
theorem: the limiting vector is the actual selected class invariant law. -/
theorem canonical_empirical_vector_ae_limit
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂canonicalPathLaw K μ.toMeasure,
      Tendsto (fun n : ℕ => empiricalVector w n) atTop
        (𝓝 (realPointMass
          (stationaryForSet K
            (CommunicatingClass K (selectedRepresentative K w))))) :=
  canonical_empirical_vector_limit_of_residual K μ
    (canonical_empirical_residual_ae_zero K μ)

end FiniteOccupationStrongLaw
end MultipleLimit
end PermanssonResearch
