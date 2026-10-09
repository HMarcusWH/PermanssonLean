import PermanssonResearch.ReverseSolver.FinitePrefixBridge
import Mathlib.Probability.Kernel.IonescuTulcea.PartialTraj

/-!
# D0-C: projectivity of the exact canonical finite-prefix law

The prefix law through T restricts *exactly* to the law through any t ≤ T.
This applies at all horizons, not merely to the one-transition marginal.
It is a building block for, not a substitute for, the target-before-danger
recursion and full rational-word/canonical-event correspondence.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver

/-- All-horizon projective consistency: the canonical path law's finite
marginals agree with the shorter canonical construction. -/
theorem rationalFiniteKernel_prefix_projective {n : ℕ}
    (M : RationalMarkovMatrix n) (y : Fin n)
    {t T : ℕ} (ht : t ≤ T) :
    (PermanssonLean.ProbabilitySupport.finitePrefixLaw
      (rationalFiniteKernel M) y T).map
      (Preorder.frestrictLe₂ ht) =
    PermanssonLean.ProbabilitySupport.finitePrefixLaw
      (rationalFiniteKernel M) y t := by
  unfold PermanssonLean.ProbabilitySupport.finitePrefixLaw
  exact Kernel.partialTraj_map_frestrictLe₂_apply
    (X := fun _ : ℕ => Fin n)
    (κ := fun k => PermanssonLean.ProbabilitySupport.stationaryPrefixKernel
      (rationalFiniteKernel M) k)
    (x₀ := PermanssonLean.ProbabilitySupport.singletonPrefix y) ht

end ReverseSolver
end PermanssonResearch
