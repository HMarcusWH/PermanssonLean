import PermanssonResearch.ReverseSolver.TypedStoppedClassEvent
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic

/-!
# C10 — stopped-class finite probabilities converge on real infinite paths

This is the genuine Ionescu–Tulcea infinite-path measure, not a numerical
surrogate.  Cramer's rational values are not yet identified with the limit:
that requires the independently proved remaining-survival error bound and
almost-sure recurrent-class entry.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open FiniteStrategicRealization
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- Exact finite-horizon stopped class-hit probabilities converge to the
measure of the genuine *infinite*-horizon stopped hit event, for every
finite rational transition matrix and starting state. -/
theorem typedStoppedClassEvent_real_tendsto {n : ℕ}
    (K : RationalMarkovMatrix n) (C : Finset (Fin n)) (x : Fin n) :
    Tendsto (fun T : ℕ => (stoppedClassHit K C T x : ℝ)) atTop
      (𝓝 (((realizedModel K).pathLaw (Measure.dirac (decode x))).real
          (⋃ T : ℕ, typedStoppedClassEvent K C T))) := by
  let P := (realizedModel K).pathLaw (Measure.dirac (decode x))
  have hcont : Tendsto
      (fun T : ℕ => P (typedStoppedClassEvent K C T)) atTop
      (𝓝 (P (⋃ T : ℕ, typedStoppedClassEvent K C T))) :=
    tendsto_measure_iUnion_atTop (μ := P)
      (typedStoppedClassEvent_monotone K C)
  have hfinite : P (⋃ T : ℕ, typedStoppedClassEvent K C T) ≠ ⊤ :=
    measure_ne_top P _
  have hreal := (ENNReal.tendsto_toReal hfinite).comp hcont
  simpa only [P, Measure.real,
    typedStoppedClassEvent_real_eq_rational] using hreal

end
end C10
end ReverseSolver
end PermanssonResearch