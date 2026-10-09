import PermanssonResearch.ReverseSolver.CanonicalFiniteKernel
import PermanssonLean.Probability.FinitePrefixTV
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj
import Mathlib.Tactic

/-!
# D0-C: canonical finite-prefix correspondence, first two horizons

The zero-transition boundary is the exact point-mass initial history.
The one-transition endpoint marginal is the actual encoded rational
Markov row. A general T-step weighted-word / finitePrefixLaw equivalence
requires a separate induction with the dependent history encoding; the
current file DOES NOT claim that universal theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver

/-- The canonical one-transition prefix has the genuine kernel as its final
state marginal, with no extra transition at time zero. -/
theorem rationalFiniteKernel_prefix_one_endpoint {n : ℕ}
    (M : RationalMarkovMatrix n) (y : Fin n) :
    (PermanssonLean.ProbabilitySupport.finitePrefixLaw
        (rationalFiniteKernel M) y 1).map
      (fun w => w ⟨1, Finset.mem_Iic.mpr le_rfl⟩) =
    rationalFiniteKernel M y := by
  let κ : (k : ℕ) → Kernel ((i : Finset.Iic k) → Fin n) (Fin n) :=
    fun k => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel
      (rationalFiniteKernel M) k
  have h := Kernel.map_partialTraj_succ_self
    (X := fun _ : ℕ => Fin n) (κ := κ) 0
  have hy := congrArg
      (fun Q : Kernel ((i : Finset.Iic 0) → Fin n) (Fin n) =>
        Q (PermanssonLean.ProbabilitySupport.singletonPrefix y)) h
  rw [Kernel.map_apply _ (by fun_prop)] at hy
  simpa [PermanssonLean.ProbabilitySupport.finitePrefixLaw,
    PermanssonLean.ProbabilitySupport.stationaryPrefixKernel,
    PermanssonLean.ProbabilitySupport.singletonPrefix, κ] using hy

/-- Every one-step singleton endpoint probability matches its rational entry. -/
theorem rationalFiniteKernel_prefix_one_singleton {n : ℕ}
    (M : RationalMarkovMatrix n) (y z : Fin n) :
    PermanssonLean.ProbabilitySupport.finitePrefixLaw
      (rationalFiniteKernel M) y 1
      {w | w ⟨1, Finset.mem_Iic.mpr le_rfl⟩ = z} =
    ENNReal.ofReal (M.entry y z : ℝ) := by
  have h := congrArg (fun μ : Measure (Fin n) => μ {z})
    (rationalFiniteKernel_prefix_one_endpoint M y)
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton z)] at h
  exact h.trans (rationalFiniteKernel_singleton M y z)

end ReverseSolver
end PermanssonResearch
