import PermanssonResearch.MultipleLimit.ExactSixStateKernelRegion
import PermanssonResearch.MultipleLimit.CanonicalClassSelector
import Mathlib.Tactic

/-!
# C53-10 — actual six-state recurrent geometry

The six-state typed alpha/P/U kernel has two transient states and two
closed recurrent blocks. Here we prove the crucial non-recurrence of
the two transients DIRECTLY for the actual typed kernel, from exact
positive transition atoms and the closed recurrent tail.

Consequently the ex-ante Boolean descriptor is true on every
recurrent state, a condition needed to certify the original proper
region's deterministic observed occupation limit without choosing
a physical recurrent class after seeing a trajectory.
-/

open MeasureTheory ProbabilityTheory

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateRecurrentGeometry

open PermanssonLean
open ReverseSolver
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateCanonical
open ExactSixStateTyped
open KernelCommunication
open RecurrentClassDecomposition

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

private theorem singleton_encode_preimage (j : Fin 6) :
    encode ⁻¹' ({j} : Set (Fin 6)) =
      ({decode j} : Set (JointState Unit (Fin 6))) := by
  ext y
  change encode y = j ↔ y = decode j
  constructor
  · intro h
    calc
      y = decode (encode y) := (decode_encode y).symm
      _ = decode j := congrArg decode h
  · intro h
    rw [h, encode_decode]

/-- Every genuine induced six-state kernel atom equals the original
rational matrix entry, as an exact ENNReal probability. -/
theorem typed_six_state_atom (i j : Fin 6) :
    typedModel.inducedKernel (decode i)
      ({decode j} : Set (JointState Unit (Fin 6))) =
        ENNReal.ofReal ((transition i j : ℚ) : ℝ) := by
  have h := typedKernel_worldCylinder i
    (E := ({j} : Set (Fin 6))) (measurableSet_singleton j)
  rw [singleton_encode_preimage] at h
  rw [rationalFiniteKernel_singleton] at h
  exact h

/-- The union of both two-state recurrent blocks excludes exactly t/u.
Its one-step closure is proved from ALL 36 actual typed kernel atoms. -/
def recurrentTail : Set (JointState Unit (Fin 6)) :=
  {y | encode y ≠ (0 : Fin 6) ∧ encode y ≠ (1 : Fin 6)}

theorem recurrentTail_closed :
    ClosedSubset typedModel.inducedKernel recurrentTail := by
  intro y hy z hed
  rcases y with ⟨u, i⟩
  rcases z with ⟨v, j⟩
  cases u
  cases v
  change 0 < typedModel.inducedKernel (decode i)
    ({decode j} : Set (JointState Unit (Fin 6))) at hed
  rw [typed_six_state_atom] at hed
  fin_cases i <;> fin_cases j <;>
    norm_num [recurrentTail, encode, transition] at *

/-- An actual positive-probability transition leaves t for u. -/
theorem t_to_u_positive :
    PositiveEdge typedModel.inducedKernel
      (decode (0 : Fin 6)) (decode (1 : Fin 6)) := by
  unfold PositiveEdge
  rw [typed_six_state_atom]
  norm_num [transition]

/-- An actual positive-probability transition leaves u for a0. -/
theorem u_to_a0_positive :
    PositiveEdge typedModel.inducedKernel
      (decode (1 : Fin 6)) (decode (2 : Fin 6)) := by
  unfold PositiveEdge
  rw [typed_six_state_atom]
  norm_num [transition]

theorem t_is_not_recurrent :
    (decode (0 : Fin 6)) ∉ RecurrentStates typedModel.inducedKernel := by
  intro ht
  have hrec : IsRecurrentState typedModel.inducedKernel (decode (0 : Fin 6)) := ht
  have h1 : decode (1 : Fin 6) ∈
      CommunicatingClass typedModel.inducedKernel (decode (0 : Fin 6)) :=
    hrec _ (mem_communicatingClass _ _) _ t_to_u_positive
  have h2 : decode (2 : Fin 6) ∈
      CommunicatingClass typedModel.inducedKernel (decode (0 : Fin 6)) :=
    hrec _ h1 _ u_to_a0_positive
  have hback : Reachable typedModel.inducedKernel
      (decode (2 : Fin 6)) (decode (0 : Fin 6)) := h2.2
  have hcontr := closed_reachable typedModel.inducedKernel
    recurrentTail_closed
    (show decode (2 : Fin 6) ∈ recurrentTail by norm_num [recurrentTail, decode, encode])
    hback
  exact (show decode (0 : Fin 6) ∉ recurrentTail by norm_num [recurrentTail, decode, encode]) hcontr

theorem u_is_not_recurrent :
    (decode (1 : Fin 6)) ∉ RecurrentStates typedModel.inducedKernel := by
  intro hu
  have hrec : IsRecurrentState typedModel.inducedKernel (decode (1 : Fin 6)) := hu
  have h2 : decode (2 : Fin 6) ∈
      CommunicatingClass typedModel.inducedKernel (decode (1 : Fin 6)) :=
    hrec _ (mem_communicatingClass _ _) _ u_to_a0_positive
  have hback : Reachable typedModel.inducedKernel
      (decode (2 : Fin 6)) (decode (1 : Fin 6)) := h2.2
  have hcontr := closed_reachable typedModel.inducedKernel
    recurrentTail_closed
    (show decode (2 : Fin 6) ∈ recurrentTail by norm_num [recurrentTail, decode, encode])
    hback
  exact (show decode (1 : Fin 6) ∉ recurrentTail by norm_num [recurrentTail, decode, encode]) hcontr

/-- The ex-ante observation is TRUE on every actual recurrent state,
including the periodic and the aperiodic class. -/
theorem recurrent_observed_true
    (y : JointState Unit (Fin 6))
    (hy : y ∈ RecurrentStates typedModel.inducedKernel) :
    observedRecurrent (encode y) = true := by
  rcases y with ⟨u, i⟩
  cases u
  fin_cases i
  · exact (t_is_not_recurrent hy).elim
  · exact (u_is_not_recurrent hy).elim
  all_goals decide

end ExactSixStateRecurrentGeometry
end MultipleLimit
end PermanssonResearch
