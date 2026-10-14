import PermanssonResearch.ReverseSolver.TypedStoppedRecurrentLimit
import PermanssonResearch.ReverseSolver.RationalFiniteStoppingBounds
import Mathlib.Tactic

/-!
# C10 — exact rational Cramer weights equal TRUE stopped-class path probabilities

The finite rational Cramer weight is squeezed between the genuine
finite-horizon path probability and its precisely bounded unabsorbed
remainder. C2 native almost-sure recurrent entry makes that remainder
converge to zero. This proves the exact, non-assumed infinite path
probability of reaching the chosen recurrent class *before* any other
recurrent class, preserving the genuine typed D0 kernel and initial state.

The remaining bridge to `pointGoodMass` groups these class-first-entry
probabilities over all true-labelled bottom classes; it is separate.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open FiniteStrategicRealization
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- Uniformly valid exact rational limits, not finite numerical approximations
or an input `exact_values` premise. -/
theorem cramerWeight_eq_typedStoppedClass_probability
    {n : ℕ} [NeZero n]
    (K : RationalMarkovMatrix n)
    (C : Finset (Fin n)) (hC : C ∈ bottomClasses K) (x : Fin n) :
    ((realizedModel K).pathLaw (Measure.dirac (decode x))).real
      (⋃ T : ℕ, typedStoppedClassEvent K C T) =
        (cramerWeight K C x : ℝ) := by
  have hFinite := typedStoppedClassEvent_real_tendsto K C x
  have hSurvival := beforeRecurrent_tendsto_zero K x
  have hLower (T : ℕ) :
      (0 : ℝ) ≤ (cramerWeight K C x : ℝ) -
        (stoppedClassHit K C T x : ℝ) := by
    exact_mod_cast (stoppedClassHit_error_le_survival K C hC T x).1
  have hUpper (T : ℕ) :
      (cramerWeight K C x : ℝ) - (stoppedClassHit K C T x : ℝ) ≤
        (beforeRecurrent K T x : ℝ) := by
    exact_mod_cast (stoppedClassHit_error_le_survival K C hC T x).2
  have hGap : Tendsto
      (fun T : ℕ => (cramerWeight K C x : ℝ) -
        (stoppedClassHit K C T x : ℝ)) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero hLower hUpper hSurvival
  have hConstant : Tendsto
      (fun _ : ℕ => (cramerWeight K C x : ℝ)) atTop
      (𝓝 (cramerWeight K C x : ℝ)) := tendsto_const_nhds
  have hDifference := hConstant.sub hGap
  have hStopped : Tendsto
      (fun T : ℕ => (stoppedClassHit K C T x : ℝ)) atTop
      (𝓝 (cramerWeight K C x : ℝ)) := by
    convert hDifference using 1
    · funext T
      ring
    · simp
  exact tendsto_nhds_unique hFinite hStopped

end
end C10
end ReverseSolver
end PermanssonResearch