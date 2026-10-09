import PermanssonResearch.ReverseSolver.CanonicalAtomMass
import Mathlib.MeasureTheory.Measure.Basic
import Mathlib.Tactic

/-!
# D0-C: exact success-event decomposition into canonical history atoms

Finite type cardinality, measurability and disjoint singleton additivity
allow the *actual* canonical finite-prefix event mass to be evaluated
as the sum of its path atoms for every horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal Classical

namespace PermanssonResearch
namespace ReverseSolver

/-- No probabilistic approximation: for each finite horizon, the actual
target-before-danger event probability is the sum over its atomic
canonical path probabilities. The weighted rational path sum needs
a further path-encoding theorem; this identity alone is not the full bridge. -/
theorem rationalFiniteKernel_success_event_atom_sum {n : ℕ}
    (M : RationalMarkovMatrix n) (target : RationalHittingTarget n)
    (y : Fin n) (T : ℕ) :
    PermanssonLean.ProbabilitySupport.finitePrefixLaw
      (rationalFiniteKernel M) y T
      (successPrefixEvent (rationalTargetAsFrozen target) T) =
    ∑ w : ((i : Finset.Iic T) → Fin n),
      if w ∈ successPrefixEvent (rationalTargetAsFrozen target) T then
        PermanssonLean.ProbabilitySupport.finitePrefixLaw
          (rationalFiniteKernel M) y T {w}
      else 0 := by
  classical
  let E : Set ((i : Finset.Iic T) → Fin n) :=
    successPrefixEvent (rationalTargetAsFrozen target) T
  let μ := PermanssonLean.ProbabilitySupport.finitePrefixLaw
    (rationalFiniteKernel M) y T
  have hfilter :
      (↑(Finset.univ.filter (fun w : ((i : Finset.Iic T) → Fin n) =>
        w ∈ E)) : Set ((i : Finset.Iic T) → Fin n)) = E := by
    ext w
    simp
  change μ E = ∑ w : ((i : Finset.Iic T) → Fin n),
    if w ∈ E then μ {w} else 0
  calc
    μ E = μ (↑(Finset.univ.filter (fun w : ((i : Finset.Iic T) → Fin n) =>
      w ∈ E)) : Set ((i : Finset.Iic T) → Fin n)) := by rw [hfilter]
    _ = ∑ w ∈ Finset.univ.filter (fun w : ((i : Finset.Iic T) → Fin n) =>
        w ∈ E), μ {w} := by rw [Measure.sum_measure_singleton]
    _ = ∑ w : ((i : Finset.Iic T) → Fin n),
      if w ∈ E then μ {w} else 0 := by
        simp [Finset.sum_filter]

end ReverseSolver
end PermanssonResearch
