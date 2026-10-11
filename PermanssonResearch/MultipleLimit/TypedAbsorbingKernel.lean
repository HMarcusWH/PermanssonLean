import PermanssonResearch.MultipleLimit.TypedStrategicWitness
import PermanssonResearch.MultipleLimit.AbsorbingFamily
import Mathlib.Tactic

/-!
# Lane C1 — actual absorbing rows of the genuine typed alpha/P/U model

This file constructs the typed witness absorbing family using the previously
proved full measure equality with the four-state rational reference.
The model is not replaced by the reference Markov chain.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedAbsorbingKernel

open TypedStrategicWitness
open PermanssonResearch.ReverseSolver
open ExactRationalAbsorption
open PermanssonLean

noncomputable section

/-- The reference a-row is an exact point mass. -/
theorem rational_a_fixed :
    rationalFiniteKernel fourStateMatrix (2 : Fin 4) =
      Measure.dirac (2 : Fin 4) := by
  apply Measure.ext_of_singleton
  intro z
  rw [rationalFiniteKernel_singleton]
  rw [Measure.dirac_apply' _ (measurableSet_singleton z)]
  fin_cases z <;> norm_num [fourStateMatrix]

/-- The reference b-row is an exact point mass. -/
theorem rational_b_fixed :
    rationalFiniteKernel fourStateMatrix (3 : Fin 4) =
      Measure.dirac (3 : Fin 4) := by
  apply Measure.ext_of_singleton
  intro z
  rw [rationalFiniteKernel_singleton]
  rw [Measure.dirac_apply' _ (measurableSet_singleton z)]
  fin_cases z <;> norm_num [fourStateMatrix]

/-- Full measure equality of the actual alpha/P/U row, not simply
a numerical claim about an isolated transition probability. -/
theorem typed_a_fixed :
    model.inducedKernel a = Measure.dirac a := by
  rw [inducedKernel_eq_rational_transport a]
  change (rationalFiniteKernel fourStateMatrix (2 : Fin 4)).map
    decodeState = Measure.dirac a
  rw [rational_a_fixed, Measure.map_dirac]
  rfl

theorem typed_b_fixed :
    model.inducedKernel b = Measure.dirac b := by
  rw [inducedKernel_eq_rational_transport b]
  change (rationalFiniteKernel fourStateMatrix (3 : Fin 4)).map
    decodeState = Measure.dirac b
  rw [rational_b_fixed, Measure.map_dirac]
  rfl

/-- Nonempty two-point absorbing family for the *literal* typed process. -/
def family : AbsorbingFamily Y where
  kernel := model.inducedKernel
  isMarkov := StrategicWorldModel.inducedKernel_isMarkov model
  absorbing := {a, b}
  absorbing_nonempty := by simp
  absorbing_fixed := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact typed_a_fixed
    · exact typed_b_fixed

/-- The finite Boolean measurable-space certificates needed by the
generic stochastic continuation and geometric-tail developments. -/
def measurableFamily : MeasurableAbsorbingFamily Y where
  family := family
  absorbing_measurable := MeasurableSet.of_discrete
  singleton_measurable := fun z => measurableSet_singleton z

end TypedAbsorbingKernel
end MultipleLimit
end PermanssonResearch
