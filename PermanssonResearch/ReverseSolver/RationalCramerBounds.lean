import PermanssonResearch.ReverseSolver.RationalCramerEquations
import PermanssonResearch.ReverseSolver.RationalHarmonicBounds
import PermanssonResearch.ReverseSolver.RationalRecurrentAccess
import Mathlib.Tactic

/-!
# C10 — exact probability-range bounds for total Cramer absorption weights

For every nonempty finite exact rational Markov matrix and each genuine
computed bottom class, Cramer's exact solution lies in [0,1] at EVERY
state. The result uses the proved graph-access maximum principle, not
floating-point root selection or sampling.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

/-- Cramer's class-destination weights are exact bounded rationals,
without any prior assumption that a candidate passed a certificate. -/
theorem cramerWeight_unit_interval {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses K) :
    ∀ x : Fin n,
      0 ≤ cramerWeight K C x ∧ cramerWeight K C x ≤ 1 := by
  apply harmonic_unit_interval K (rationalRecurrentUnion K)
    (every_state_reaches_rational_recurrent K)
    (cramerWeight K C)
  · intro y hy
    rw [cramerWeight_boundary K C y hy]
    split_ifs <;> norm_num
  · intro y hy
    exact cramerWeight_transient_harmonic K C hC y hy

end C10
end ReverseSolver
end PermanssonResearch