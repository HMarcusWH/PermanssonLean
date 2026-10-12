import PermanssonResearch.MultipleLimit.FiniteInvariantUniqueness
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# Lane C2 — general finite Markov kernel to REAL stochastic rows

Do not identify a rational reference matrix with the actual infinite
Markov model. Instead, an arbitrary genuine probability kernel K on a
finite measurable space induces an exact REAL row-stochastic matrix
by reading each measurable singleton mass, including irrational values.

The row normalization is proved using finite measure additivity and
ENNReal.toReal_sum; the real stationary-distribution existence result
can then be applied to this exact array.

The further REAL-vector to ENNReal invariant-MEASURE transport is
a distinct following lemma, not assumed as part of this interface.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteKernelRealBridge

variable {Y : Type*} [MeasurableSpace Y] [Fintype Y]
variable [MeasurableSingletonClass Y]
variable (K : Kernel Y Y) [IsMarkovKernel K]

noncomputable def realTransition (i j : Y) : ℝ :=
  (K i ({j} : Set Y)).toReal

theorem realTransition_nonneg (i j : Y) :
    0 ≤ realTransition K i j :=
  ENNReal.toReal_nonneg

theorem kernel_singleton_ne_top (i j : Y) :
    K i ({j} : Set Y) ≠ ∞ := by
  letI : IsProbabilityMeasure (K i) :=
    IsMarkovKernel.isProbabilityMeasure i
  exact measure_ne_top (K i) _

theorem realTransition_row_sum (i : Y) :
    (∑ j : Y, realTransition K i j) = 1 := by
  classical
  have hsum :
      (∑ j : Y, K i ({j} : Set Y)) = K i Set.univ := by
    simpa using (sum_measure_singleton
      (μ := K i) (s := (Finset.univ : Finset Y)))
  change (∑ j : Y, (K i ({j} : Set Y)).toReal) = 1
  rw [← ENNReal.toReal_sum (fun j hj => kernel_singleton_ne_top K i j)]
  rw [hsum]
  haveI : IsProbabilityMeasure (K i) :=
    IsMarkovKernel.isProbabilityMeasure i
  simp

/-- The source probability kernel yields a stationary REAL row-vector
without any assumed invariant measure or rationality hypothesis. This
claim is about the genuine single-step masses converted to real. -/
theorem exists_stationary_real_of_kernel [Nonempty Y] :
    ∃ π : Y → ℝ,
      (∀ j, 0 ≤ π j) ∧
      (∑ j : Y, π j) = 1 ∧
      ∀ j, FiniteCesaroAlgebra.pushVector
        (realTransition K) π j = π j :=
  FiniteInvariantExistence.exists_stationary_real
    (realTransition K)
    (realTransition_nonneg K)
    (realTransition_row_sum K)

end FiniteKernelRealBridge
end MultipleLimit
end PermanssonResearch
