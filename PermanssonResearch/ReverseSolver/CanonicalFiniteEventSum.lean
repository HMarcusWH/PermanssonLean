import PermanssonResearch.ReverseSolver.CanonicalWordMass
import Mathlib.Tactic

/-!
# D0-C: canonical success probability is exactly the weighted vector sum

The calculation is performed on the actual mathlib finitePrefixLaw.
An equivalence reindexes all paths by their time-zero state and successor
vector; the canonical kernel assigns zero to paths not starting at y.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ReverseSolver

/-- A finite-horizon canonical success event has exactly the sum of the
transition-product weights of successful successor vectors. -/
theorem rationalFiniteKernel_success_eq_vector_weight_sum {n : ℕ}
    (M : RationalMarkovMatrix n) (target : RationalHittingTarget n)
    (T : ℕ) (y : Fin n) :
    PermanssonLean.ProbabilitySupport.finitePrefixLaw
        (rationalFiniteKernel M) y T
        (successPrefixEvent (rationalTargetAsFrozen target) T) =
    ∑ v : Fin T → Fin n,
      if successorWordWins target y (List.ofFn v) then
        canonicalHistoryWeight M T (historyFromSteps T y v)
      else 0 := by
  classical
  let μ := PermanssonLean.ProbabilitySupport.finitePrefixLaw
    (rationalFiniteKernel M) y T
  let E := successPrefixEvent (rationalTargetAsFrozen target) T
  have hatom := rationalFiniteKernel_success_event_atom_sum M target y T
  change μ E = _ at hatom
  rw [hatom]
  change
    (∑ w : ((i : Finset.Iic T) → Fin n),
      if w ∈ E then μ {w} else 0) = _
  calc
    (∑ w : ((i : Finset.Iic T) → Fin n),
        if w ∈ E then μ {w} else 0) =
      ∑ p : Fin n × (Fin T → Fin n),
        if historyFromSteps T p.1 p.2 ∈ E then
          μ {historyFromSteps T p.1 p.2} else 0 := by
          symm
          apply Fintype.sum_equiv (fullHistoryEquiv (n := n) T)
          intro p
          rfl
    _ = ∑ v : Fin T → Fin n,
        if historyFromSteps T y v ∈ E then
          canonicalHistoryWeight M T (historyFromSteps T y v)
        else 0 := by
          rw [Fintype.sum_prod_type, Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro v hv
          have hmass (x : Fin n) :
              μ {historyFromSteps T x v} =
                if x = y then
                  canonicalHistoryWeight M T (historyFromSteps T x v)
                else 0 := by
              simpa [μ, historyFromSteps_initial] using
                (rationalFiniteKernel_prefix_atom_product M y T
                  (historyFromSteps T x v))
          calc
            (∑ x : Fin n,
              if historyFromSteps T x v ∈ E then
                μ {historyFromSteps T x v} else 0) =
              ∑ x : Fin n,
                if x = y then
                  (if historyFromSteps T x v ∈ E then
                    canonicalHistoryWeight M T (historyFromSteps T x v)
                  else 0) else 0 := by
                    apply Finset.sum_congr rfl
                    intro x hx
                    rw [hmass]
                    by_cases he : x = y <;> simp [he]
            _ = if historyFromSteps T y v ∈ E then
                  canonicalHistoryWeight M T (historyFromSteps T y v)
                else 0 := by simp
    _ = ∑ v : Fin T → Fin n,
        if successorWordWins target y (List.ofFn v) then
          canonicalHistoryWeight M T (historyFromSteps T y v)
        else 0 := by
          apply Finset.sum_congr rfl
          intro v hv
          exact if_congr (canonicalSuccess_iff_wordWins target T y v) rfl rfl

end ReverseSolver
end PermanssonResearch
