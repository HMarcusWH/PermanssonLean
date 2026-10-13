import PermanssonResearch.MultipleLimit.ExactSixStateC8SupportWitness
import PermanssonResearch.MultipleLimit.ExactSixStateC7Witness
import Mathlib.Tactic

/-!
# C8 — formal negative controls on overstrong support claims

Matching positive transition support must NOT be called equality of
induced Markov kernels, selection probabilities, full infinite path
laws or numerical constitutive margins. Two ACTUAL typed alpha/P/U
interventions have equal support but unequal one-step probability atoms.

C7's already compiled original six-state periodic A class with mixed
Boolean labels is reused as a second FORMAL negative control.
Numeric differing margins are recomputed independently with exact
Fractions in test_lane_c8_support_graph.py; no uncompiled margin
theorem is claimed here.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteSupportCounterexamples

set_option autoImplicit false

open PermanssonLean
open ReverseSolver.FiniteStrategicRealization
open ExactSixStateTyped
open ExactSixStateC8SupportWitness
open ExactSixStateC7Witness
open ExactSixStateCanonical
open ObservedSupportInvariance

noncomputable section

/-- The a0-to-false-u atom has exact rational values 1/2 and 1/1000,
despite the two six-state kernels having the same strictly positive
support graph. -/
theorem unequal_typed_intervention_atom :
    halfJ.intervention.apply.inducedKernel
      (decode (2 : Fin 6))
      ({decode (1 : Fin 6)} : Set (JointState Unit (Fin 6))) ≠
    tinyJ.intervention.apply.inducedKernel
      (decode (2 : Fin 6))
      ({decode (1 : Fin 6)} : Set (JointState Unit (Fin 6))) := by
  rw [half_atom, tiny_atom]
  norm_num [halfEntry, tinyEntry, softEntry]

/-- Full equality of kernels is strictly stronger than equality of
their positive edge supports. Both kernels come from actual admissible
strategic alpha replacements with common P and U, not fabricated
standalone reference kernels. -/
theorem support_equal_but_actual_kernels_distinct :
    SamePositiveSupport
      halfJ.intervention.apply.inducedKernel
      tinyJ.intervention.apply.inducedKernel ∧
    halfJ.intervention.apply.inducedKernel ≠
      tinyJ.intervention.apply.inducedKernel := by
  refine ⟨same_intervened_positive_support, ?_⟩
  intro hEq
  apply unequal_typed_intervention_atom
  exact congrArg
    (fun κ : Kernel (JointState Unit (Fin 6)) (JointState Unit (Fin 6)) =>
      κ (decode (2 : Fin 6))
        ({decode (1 : Fin 6)} : Set (JointState Unit (Fin 6))))
    hEq

/-- A periodic class with a genuine mixed Boolean observation is NOT
good, even though its physical empirical occupation converges a.s. -/
theorem periodic_A_mixed_labels_not_good :
    ¬ FiniteObservedClassSupport.AllTrueClass
      typedModel.inducedKernel mixedDescriptor (decode (2 : Fin 6)) :=
  mixed_periodic_A_not_good

end
end FiniteSupportCounterexamples
end MultipleLimit
end PermanssonResearch
