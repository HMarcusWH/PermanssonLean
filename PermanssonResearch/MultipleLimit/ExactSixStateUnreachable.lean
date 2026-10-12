import PermanssonResearch.MultipleLimit.ExactSixStateClassLaws
import Mathlib.Tactic

/-!
# Lane C2 — actual-kernel six-state unreachable-class negative controls

Positive-edge reachability is restricted by real graph closure:
a trajectory beginning in recurrent class A cannot follow ANY
positive-probability edge path to class B, or conversely. These
are proofs about the actual typed alpha/P/U-induced kernel, rather
than just zero entries in a separately declared rational matrix.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateUnreachable

open ReverseSolver.FiniteStrategicRealization
open ExactSixStateTyped
open ExactSixStateClassSelectionWeights
open ExactSixStateClassLaws
open ExactSixState
open KernelCommunication

/-- The period-two physical class cannot communicate with the
distinct aperiodic class in the actual Markov kernel. -/
theorem A_cannot_reach_B :
    ¬ Reachable typedModel.inducedKernel
      (decode (2 : Fin 6)) (decode (4 : Fin 6)) := by
  intro h
  have h2 : decode (2 : Fin 6) ∈ classASet := by
    simp [classASet, classA, encode, decode]
  have h4 := closed_reachable typedModel.inducedKernel
    classASet_closed h2 h
  have hnot : decode (4 : Fin 6) ∉ classASet := by
    simp [classASet, classA, encode, decode]
  exact hnot h4

/-- Reverse unreachable-class negative control, also using the
genuine kernel's closed recurrent B block. -/
theorem B_cannot_reach_A :
    ¬ Reachable typedModel.inducedKernel
      (decode (4 : Fin 6)) (decode (2 : Fin 6)) := by
  intro h
  have h4 : decode (4 : Fin 6) ∈ classBSet := by
    simp [classBSet, classB, encode, decode]
  have h2 := closed_reachable typedModel.inducedKernel
    classBSet_closed h4 h
  have hnot : decode (2 : Fin 6) ∉ classBSet := by
    simp [classBSet, classB, encode, decode]
  exact hnot h2

/-- Two consecutive finite-periodic rows really differ in the
typed model. Consequently one-step marginals cannot be substituted
for the period-two class stationary occupation law. -/
theorem periodic_rows_not_equal :
    typedModel.inducedKernel (decode (2 : Fin 6)) ≠
      typedModel.inducedKernel (decode (3 : Fin 6)) := by
  intro h
  have hx := congrArg
    (fun ρ : Measure (PermanssonLean.JointState Unit (Fin 6)) =>
      ρ ({decode (2 : Fin 6)} : Set _)) h
  rw [ExactSixStateRecurrentGeometry.typed_six_state_atom,
      ExactSixStateRecurrentGeometry.typed_six_state_atom] at hx
  norm_num [transition] at hx

end ExactSixStateUnreachable
end MultipleLimit
end PermanssonResearch
