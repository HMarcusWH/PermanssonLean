import PermanssonResearch.ReverseSolver.RationalKernel
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.Probability.Kernel.Basic
import Mathlib.Tactic

/-!
# D0-C: exact finite rational rows as a genuine canonical Markov kernel

This construction creates a kernel on the finite discrete state space, not an
admissible strategic-world intervention. The world-transition primitive P has
no representation in this standalone matrix layer.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver

/-- A finite rational stochastic matrix interpreted as a probability kernel,
with the row measure represented as a finite weighted sum of Dirac measures. -/
noncomputable def rationalFiniteKernel {n : ℕ} (M : RationalMarkovMatrix n) :
    Kernel (Fin n) (Fin n) where
  toFun := fun y =>
    ∑ z : Fin n, (ENNReal.ofReal (M.entry y z : ℝ)) • Measure.dirac z
  measurable' := Measurable.of_discrete

/-- One-step atomic probabilities are precisely the encoded rational entries. -/
theorem rationalFiniteKernel_singleton {n : ℕ}
    (M : RationalMarkovMatrix n) (y z : Fin n) :
    rationalFiniteKernel M y {z} = ENNReal.ofReal (M.entry y z : ℝ) := by
  classical
  simp [rationalFiniteKernel, Measure.finsetSum_apply, Measure.smul_apply]

/-- The canonical kernel is Markov because each certified row sums to one. -/
instance rationalFiniteKernel_isMarkov {n : ℕ}
    (M : RationalMarkovMatrix n) : IsMarkovKernel (rationalFiniteKernel M) := by
  refine ⟨fun y => ⟨?_⟩⟩
  have hreal : (∑ z : Fin n, (M.entry y z : ℝ)) = 1 := by
    exact_mod_cast M.row_sum_one y
  have hnonneg : ∀ z ∈ (Finset.univ : Finset (Fin n)),
      0 ≤ (M.entry y z : ℝ) := by
    intro z _
    exact_mod_cast M.entry_nonneg y z
  change (∑ z : Fin n, (ENNReal.ofReal (M.entry y z : ℝ)) •
    Measure.dirac z) Set.univ = 1
  simp only [Measure.finsetSum_apply, Measure.smul_apply]
  simp only [Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun z _ => hnonneg z (Finset.mem_univ z))]
  rw [hreal]
  simp

end ReverseSolver
end PermanssonResearch
