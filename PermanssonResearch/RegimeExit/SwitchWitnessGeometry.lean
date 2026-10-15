import PermanssonResearch.RegimeExit.SwitchWitnessModels
import PermanssonResearch.MultipleLimit.FiniteEventuallyObserved
import PermanssonResearch.MultipleLimit.FiniteClassClosure
import PermanssonResearch.MultipleLimit.FiniteExactGRRecovery
import Mathlib.Tactic

/-!
# C-Exit B — actual recurrent geometry and invariance of the 5-state witness

All edges are proved from the literal alpha/P/U-induced kernels using
the certified rational realization. The two terminal classes {3},{4}
are shared, but their regime regions and initial basins are different.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PermanssonResearch.RegimeExit.SwitchWitnessGeometry

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.ReverseSolver
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.MultipleLimit
open PermanssonResearch.MultipleLimit.KernelCommunication
open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
open PermanssonResearch.RegimeExit.SwitchWitnessModels

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

private theorem singleton_encode_preimage (j : Fin 5) :
    encode ⁻¹' ({j} : Set (Fin 5)) =
      ({decode j} : Set Y) := by
  ext y
  change encode y = j ↔ y = decode j
  constructor
  · intro h
    calc
      y = decode (encode y) := (decode_encode y).symm
      _ = decode j := congrArg decode h
  · intro h
    rw [h, encode_decode]

/-- Literal rational entry equals the induced, genuine point-to-point
Markov transition under the constructed strategic-world model. -/
theorem typed_five_atom (K : RationalMarkovMatrix 5)
    (i j : Fin 5) :
    (realizedModel K).inducedKernel (decode i)
      ({decode j} : Set Y) =
        ENNReal.ofReal ((K.entry i j : ℚ) : ℝ) := by
  have h := inducedKernel_encodedEntry K i j
  rw [singleton_encode_preimage] at h
  exact h

/-- The only terminal states are 3 and 4, both absorbing in either
model. This closure is a proof on ALL actual induced 5×5 atoms. -/
def terminalTail : Set Y :=
  {y | encode y = (3 : Fin 5) ∨ encode y = (4 : Fin 5)}

theorem baseline_terminal_closed :
    ClosedSubset baselineModel.inducedKernel terminalTail := by
  intro y hy z hed
  rcases y with ⟨u,i⟩
  rcases z with ⟨v,j⟩
  cases u
  cases v
  change 0 < (realizedModel baselineMatrix).inducedKernel
    (decode i) ({decode j} : Set Y) at hed
  rw [typed_five_atom baselineMatrix i j] at hed
  fin_cases i <;> fin_cases j <;>
    norm_num [terminalTail, encode, baselineMatrix] at *

theorem full_terminal_closed :
    ClosedSubset fullModel.inducedKernel terminalTail := by
  intro y hy z hed
  rcases y with ⟨u,i⟩
  rcases z with ⟨v,j⟩
  cases u
  cases v
  change 0 < (realizedModel fullMatrix).inducedKernel
    (decode i) ({decode j} : Set Y) at hed
  rw [typed_five_atom fullMatrix i j] at hed
  fin_cases i <;> fin_cases j <;>
    norm_num [terminalTail, encode, fullMatrix] at *

/-- A positive atom into a closed block and no return implies that the
starting state is NOT recurrent. -/
private theorem nonrecurrent_if_positive_into_closed
    (K : Kernel Y Y) (C : Set Y) (hC : ClosedSubset K C)
    (x z : Y) (hx : x ∉ C) (hz : z ∈ C)
    (hxz : PositiveEdge K x z) :
    x ∉ RecurrentStates K := by
  intro hrec
  have hClosed : IsRecurrentState K x := hrec
  have hzClass : z ∈ CommunicatingClass K x :=
    hClosed _ (mem_communicatingClass K x) _ hxz
  have hBack : Reachable K z x := hzClass.2
  exact hx (closed_reachable K hC hz hBack)

/-- A positive 2-step route into a closed block also excludes recurrence
at the starting state (the reverse route cannot leave the block). -/
private theorem nonrecurrent_if_two_positive_into_closed
    (K : Kernel Y Y) (C : Set Y) (hC : ClosedSubset K C)
    (x z t : Y) (hx : x ∉ C) (ht : t ∈ C)
    (hxz : PositiveEdge K x z)
    (hzt : PositiveEdge K z t) :
    x ∉ RecurrentStates K := by
  intro hrec
  have hClosed : IsRecurrentState K x := hrec
  have hzClass : z ∈ CommunicatingClass K x :=
    hClosed _ (mem_communicatingClass K x) _ hxz
  have htClass : t ∈ CommunicatingClass K x :=
    hClosed _ hzClass _ hzt
  have hBack : Reachable K t x := htClass.2
  exact hx (closed_reachable K hC ht hBack)

theorem baseline_edge_01 :
    PositiveEdge baselineModel.inducedKernel (decode (0 : Fin 5))
      (decode (1 : Fin 5)) := by
  unfold PositiveEdge
  change 0 < (realizedModel baselineMatrix).inducedKernel (decode 0)
    ({decode 1} : Set Y)
  rw [typed_five_atom]
  norm_num [baselineMatrix]

theorem baseline_edge_14 :
    PositiveEdge baselineModel.inducedKernel (decode (1 : Fin 5))
      (decode (4 : Fin 5)) := by
  unfold PositiveEdge
  change 0 < (realizedModel baselineMatrix).inducedKernel (decode 1)
    ({decode 4} : Set Y)
  rw [typed_five_atom]
  norm_num [baselineMatrix]

theorem baseline_edge_23 :
    PositiveEdge baselineModel.inducedKernel (decode (2 : Fin 5))
      (decode (3 : Fin 5)) := by
  unfold PositiveEdge
  change 0 < (realizedModel baselineMatrix).inducedKernel (decode 2)
    ({decode 3} : Set Y)
  rw [typed_five_atom]
  norm_num [baselineMatrix]

theorem full_edge_02 :
    PositiveEdge fullModel.inducedKernel (decode (0 : Fin 5))
      (decode (2 : Fin 5)) := by
  unfold PositiveEdge
  change 0 < (realizedModel fullMatrix).inducedKernel (decode 0)
    ({decode 2} : Set Y)
  rw [typed_five_atom]
  norm_num [fullMatrix]

theorem full_edge_13 :
    PositiveEdge fullModel.inducedKernel (decode (1 : Fin 5))
      (decode (3 : Fin 5)) := by
  unfold PositiveEdge
  change 0 < (realizedModel fullMatrix).inducedKernel (decode 1)
    ({decode 3} : Set Y)
  rw [typed_five_atom]
  norm_num [fullMatrix]

theorem full_edge_23 :
    PositiveEdge fullModel.inducedKernel (decode (2 : Fin 5))
      (decode (3 : Fin 5)) := by
  unfold PositiveEdge
  change 0 < (realizedModel fullMatrix).inducedKernel (decode 2)
    ({decode 3} : Set Y)
  rw [typed_five_atom]
  norm_num [fullMatrix]

theorem baseline_zero_not_recurrent :
    decode (0 : Fin 5) ∉ RecurrentStates baselineModel.inducedKernel :=
  nonrecurrent_if_two_positive_into_closed baselineModel.inducedKernel
    terminalTail baseline_terminal_closed (decode 0) (decode 1)
    (decode 4) (by decide) (by decide)
    baseline_edge_01 baseline_edge_14

theorem baseline_one_not_recurrent :
    decode (1 : Fin 5) ∉ RecurrentStates baselineModel.inducedKernel :=
  nonrecurrent_if_positive_into_closed baselineModel.inducedKernel
    terminalTail baseline_terminal_closed (decode 1)
    (decode 4) (by decide) (by decide) baseline_edge_14

theorem baseline_two_not_recurrent :
    decode (2 : Fin 5) ∉ RecurrentStates baselineModel.inducedKernel :=
  nonrecurrent_if_positive_into_closed baselineModel.inducedKernel
    terminalTail baseline_terminal_closed (decode 2)
    (decode 3) (by decide) (by decide) baseline_edge_23

theorem full_zero_not_recurrent :
    decode (0 : Fin 5) ∉ RecurrentStates fullModel.inducedKernel :=
  nonrecurrent_if_two_positive_into_closed fullModel.inducedKernel
    terminalTail full_terminal_closed (decode 0) (decode 2)
    (decode 3) (by decide) (by decide) full_edge_02 full_edge_23

theorem full_one_not_recurrent :
    decode (1 : Fin 5) ∉ RecurrentStates fullModel.inducedKernel :=
  nonrecurrent_if_positive_into_closed fullModel.inducedKernel
    terminalTail full_terminal_closed (decode 1)
    (decode 3) (by decide) (by decide) full_edge_13

theorem full_two_not_recurrent :
    decode (2 : Fin 5) ∉ RecurrentStates fullModel.inducedKernel :=
  nonrecurrent_if_positive_into_closed fullModel.inducedKernel
    terminalTail full_terminal_closed (decode 2)
    (decode 3) (by decide) (by decide) full_edge_23

/-- A genuinely nonconstant descriptor on BOTH declared regime regions:
false at their transient input states and true at either terminal state. -/
def observed (y : Y) : Bool :=
  decide (encode y = (3 : Fin 5) ∨ encode y = (4 : Fin 5))

theorem baseline_recurrent_observed_true
    (y : Y) (hy : y ∈ RecurrentStates baselineModel.inducedKernel) :
    observed y = true := by
  rcases y with ⟨u,i⟩
  cases u
  fin_cases i
  · exact (baseline_zero_not_recurrent hy).elim
  · exact (baseline_one_not_recurrent hy).elim
  · exact (baseline_two_not_recurrent hy).elim
  all_goals decide

theorem full_recurrent_observed_true
    (y : Y) (hy : y ∈ RecurrentStates fullModel.inducedKernel) :
    observed y = true := by
  rcases y with ⟨u,i⟩
  cases u
  fin_cases i
  · exact (full_zero_not_recurrent hy).elim
  · exact (full_one_not_recurrent hy).elim
  · exact (full_two_not_recurrent hy).elim
  all_goals decide

theorem source_region_closed :
    ClosedSubset baselineModel.inducedKernel sourceSpec.region := by
  intro y hy z hed
  rcases y with ⟨u,i⟩
  rcases z with ⟨v,j⟩
  cases u
  cases v
  change 0 < (realizedModel baselineMatrix).inducedKernel
    (decode i) ({decode j} : Set Y) at hed
  rw [typed_five_atom baselineMatrix i j] at hed
  fin_cases i <;> fin_cases j <;>
    norm_num [sourceSpec, encode, baselineMatrix] at *

theorem target_region_closed :
    ClosedSubset fullModel.inducedKernel targetSpec.region := by
  intro y hy z hed
  rcases y with ⟨u,i⟩
  rcases z with ⟨v,j⟩
  cases u
  cases v
  change 0 < (realizedModel fullMatrix).inducedKernel
    (decode i) ({decode j} : Set Y) at hed
  rw [typed_five_atom fullMatrix i j] at hed
  fin_cases i <;> fin_cases j <;>
    norm_num [targetSpec, encode, fullMatrix] at *

theorem source_exactlyInvariant :
    IsExactlyInvariant baselineModel sourceSpec := by
  intro y hy
  exact FiniteClassClosure.closedSubset_kernel_mass_one
    baselineModel.inducedKernel sourceSpec.region source_region_closed y hy

theorem target_exactlyInvariant :
    IsExactlyInvariant fullModel targetSpec := by
  intro y hy
  exact FiniteClassClosure.closedSubset_kernel_mass_one
    fullModel.inducedKernel targetSpec.region target_region_closed y hy

end PermanssonResearch.RegimeExit.SwitchWitnessGeometry
