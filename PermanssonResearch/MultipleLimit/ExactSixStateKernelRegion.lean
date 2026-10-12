import PermanssonResearch.MultipleLimit.ExactSixStateRegion
import PermanssonResearch.MultipleLimit.ExactSixStateTyped
import PermanssonResearch.ReverseSolver.FiniteStrategicRealization
import Mathlib.Tactic

/-!
# C53-14 — true typed six-state proper-region invariance

The matrix has zero one-step probability of returning to state t=0 from
any state.  Transport this EXACT zero through the previously certified
alpha/P/U-induced kernel and conclude that the proper region excluding t
is exactly invariant in the sense of the frozen regime definition.

This is a property of the genuine typed Markov kernel, not only a rational
reference matrix.  The separate nontriviality and eventual observation
arguments complete the original GR gates later.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateKernelRegion

open PermanssonLean
open ReverseSolver
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateCanonical
open ExactSixStateTyped

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

def typedRegion : Set (JointState Unit (Fin 6)) :=
  encode ⁻¹' ExactSixStateRegion.region

theorem rational_no_entry_zero (i : Fin 6) :
    rationalFiniteKernel sixStateMatrix i ({0} : Set (Fin 6)) = 0 := by
  rw [rationalFiniteKernel_singleton sixStateMatrix i (0 : Fin 6)]
  fin_cases i <;> norm_num [sixStateMatrix, transition]

theorem singleton_zero_preimage :
    encode ⁻¹' ({0} : Set (Fin 6)) =
      ({decode (0 : Fin 6)} : Set (JointState Unit (Fin 6))) := by
  ext y
  rcases y with ⟨u, i⟩
  cases u
  simp [decode, encode]

theorem typed_no_entry_zero (i : Fin 6) :
    typedModel.inducedKernel (decode i)
      ({decode (0 : Fin 6)} : Set (JointState Unit (Fin 6))) = 0 := by
  have h := typedKernel_worldCylinder i
    (E := ({0} : Set (Fin 6))) (measurableSet_singleton (0 : Fin 6))
  rw [singleton_zero_preimage, rational_no_entry_zero i] at h
  exact h

theorem typed_no_entry_zero_all (y : JointState Unit (Fin 6)) :
    typedModel.inducedKernel y
      ({decode (0 : Fin 6)} : Set (JointState Unit (Fin 6))) = 0 := by
  simpa only [decode_encode] using typed_no_entry_zero (encode y)

theorem typedRegion_eq_compl_singleton :
    typedRegion =
      ({decode (0 : Fin 6)} : Set (JointState Unit (Fin 6)))ᶜ := by
  ext y
  rw [show typedRegion = encode ⁻¹' ({i : Fin 6 | i ≠ 0}) from rfl]
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_compl_iff,
    Set.mem_singleton_iff]
  constructor
  · intro h heq
    apply h
    simpa only [encode_decode] using congrArg encode heq
  · intro h heq
    apply h
    have hn := congrArg decode heq
    simpa only [decode_encode] using hn

theorem typed_region_measurable : MeasurableSet typedRegion :=
  (Set.toFinite typedRegion).measurableSet

/-- Genuine original-model Markov invariance for the proper five-state
region, valid even for the excluded transient initial point. -/
theorem typedRegion_kernel_mass_one
    (y : JointState Unit (Fin 6)) :
    typedModel.inducedKernel y typedRegion = 1 := by
  letI : IsMarkovKernel typedModel.inducedKernel :=
    PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov _
  rw [typedRegion_eq_compl_singleton]
  rw [prob_compl_eq_one_sub (measurableSet_singleton (decode (0 : Fin 6)))]
  rw [typed_no_entry_zero_all y]
  simp

end ExactSixStateKernelRegion
end MultipleLimit
end PermanssonResearch
