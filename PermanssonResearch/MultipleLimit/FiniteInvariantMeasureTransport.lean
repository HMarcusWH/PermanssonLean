import PermanssonResearch.MultipleLimit.FiniteKernelRealBridge
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Probability.Kernel.Invariance
import Mathlib.Tactic

/-!
# Lane C2 — finite REAL invariant row vectors as genuine Markov measures

The weights of an arbitrary finite real probability vector are encoded
as the actual ENNReal-weighted Dirac measure on the original measurable
state space Y. The construction is exactly normalized, and exact
real stationarity gives equality of WHOLE measures K ∘ₘ π = π.

Together with the separate compactness proof for real stationary
vectors, this yields existence of a TRUE stationary probability measure
for an arbitrary nonempty finite homogeneous Markov kernel, including
irrational entries and periodic/nonirreducible chains.

This is global stationary existence; the unique class-supported
law and the a.s. empirical occupation theorem remain separate tasks.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteInvariantMeasureTransport

open FiniteKernelRealBridge
open FiniteCesaroAlgebra

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]

/-- The genuine measure corresponding to a finite real nonnegative
row vector, preserving the exact original measurable atoms. -/
noncomputable def vectorMeasure (v : Y → ℝ) : Measure Y :=
  ∑ i : Y, ENNReal.ofReal (v i) • Measure.dirac i

theorem vectorMeasure_singleton (v : Y → ℝ) (j : Y) :
    vectorMeasure v {j} = ENNReal.ofReal (v j) := by
  classical
  simp [vectorMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Pi.single_apply]

/-- Real normalization transports to probability-one in ENNReal. -/
theorem vectorMeasure_isProbability
    (v : Y → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hvtotal : (∑ i : Y, v i) = 1) :
    IsProbabilityMeasure (vectorMeasure v) := by
  refine ⟨?_⟩
  change (∑ i : Y, (ENNReal.ofReal (v i)) •
    Measure.dirac i) Set.univ = 1
  simp only [Measure.finsetSum_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply,
    smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => hv i)]
  rw [hvtotal]
  simp

/-- Under exact stationary real matrix equations, the actual
ENNReal probability measure is invariant for the actual Markov
kernel. Equality is proved on all measurable events via atoms. -/
theorem vectorMeasure_invariant
    (K : Kernel Y Y) [IsMarkovKernel K]
    (v : Y → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hstat : ∀ j, pushVector (realTransition K) v j = v j) :
    Kernel.Invariant K (vectorMeasure v) := by
  apply Measure.ext_of_singleton
  intro j
  change (vectorMeasure v).bind K {j} = vectorMeasure v {j}
  rw [Measure.bind_apply (measurableSet_singleton j) (Kernel.aemeasurable K)]
  have hcalc :
      (∫⁻ i, K i ({j} : Set Y) ∂(vectorMeasure v)) =
      ∑ i : Y, ENNReal.ofReal (v i) * K i ({j} : Set Y) := by
    classical
    unfold vectorMeasure
    rw [lintegral_finsetSum_measure]
    apply Finset.sum_congr rfl
    intro i hi
    rw [lintegral_smul_measure, lintegral_dirac' i
      (Kernel.measurable_coe K (measurableSet_singleton j))]
    rfl
  rw [hcalc, vectorMeasure_singleton]
  calc
    (∑ i : Y, ENNReal.ofReal (v i) * K i ({j} : Set Y)) =
        ∑ i : Y, ENNReal.ofReal (v i * realTransition K i j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [show K i ({j} : Set Y) =
          ENNReal.ofReal (realTransition K i j) from
        (ENNReal.ofReal_toReal (kernel_singleton_ne_top K i j)).symm]
      rw [ENNReal.ofReal_mul (hv i)]
    _ = ENNReal.ofReal (pushVector (realTransition K) v j) := by
      unfold pushVector
      rw [ENNReal.ofReal_sum_of_nonneg
        (fun i hi => mul_nonneg (hv i) (realTransition_nonneg K i j))]
    _ = ENNReal.ofReal (v j) := by rw [hstat j]

/-- An unconditional *genuine measure-level* stationary probability
exists for EVERY nonempty finite homogeneous Markov kernel.
No irreducibility, aperiodicity or pre-existing π supplied. -/
theorem exists_stationary_probability
    (K : Kernel Y Y) [IsMarkovKernel K] [Nonempty Y] :
    ∃ μ : Measure Y,
      IsProbabilityMeasure μ ∧ Kernel.Invariant K μ := by
  obtain ⟨v, hv, htotal, hstat⟩ :=
    exists_stationary_real_of_kernel K
  refine ⟨vectorMeasure v, vectorMeasure_isProbability v hv htotal, ?_⟩
  exact vectorMeasure_invariant K v hv hstat

end FiniteInvariantMeasureTransport
end MultipleLimit
end PermanssonResearch
