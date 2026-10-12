import PermanssonResearch.MultipleLimit.ExactSixStateClassLaws
import PermanssonResearch.MultipleLimit.FiniteInvariantMeasureTransport
import Mathlib.Tactic

/-!
# C55-01 — exact coordinates of the TRUE typed six-state stationary laws

The two measures `ExactSixStateClassLaws.πA` and `πB` were defined by
an existential classwise uniqueness construction. The rational functions
`ExactSixState.piA/piB` were proved invariant for a separate rational
matrix. This module connects those objects through the GENUINE alpha/P/U
induced kernel, constructs exact class-supported probability measures,
and invokes the EXISTING uniqueness theorem to identify entire measures.

No stationary measures are replaced by declaration. No global
irreducibility or aperiodicity assumption is imposed on the chain.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateStationaryCoordinates

open PermanssonLean
open ReverseSolver.FiniteStrategicRealization
open ExactSixState
open ExactSixStateTyped
open ExactSixStateRecurrentGeometry
open ExactSixStateClassSelectionWeights
open ExactSixStateClassLaws
open FiniteKernelRealBridge
open FiniteCesaroAlgebra
open FiniteInvariantMeasureTransport
open FiniteClassInvariantMeasure

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

abbrev SixY := JointState Unit (Fin 6)
private noncomputable abbrev K := typedModel.inducedKernel

/-- The actual typed alpha/P/U singleton matrix equals the rational
reference matrix after the exact ENNReal-to-real conversion. -/
theorem realTransition_typed_six_state (i j : Fin 6) :
    realTransition K (decode i) (decode j) =
      ((transition i j : ℚ) : ℝ) := by
  change (K (decode i) ({decode j} : Set SixY)).toReal = _
  rw [typed_six_state_atom]
  exact ENNReal.toReal_ofReal
    (show 0 ≤ ((transition i j : ℚ) : ℝ) by
      exact_mod_cast transition_nonneg i j)

/-- Original exact stationary rational vector, transported along the
proved `encode` coordinate equivalence into the real typed state. -/
def realPiA (y : SixY) : ℝ := ((piA (encode y) : ℚ) : ℝ)
def realPiB (y : SixY) : ℝ := ((piB (encode y) : ℚ) : ℝ)

theorem realPiA_nonneg (y : SixY) : 0 ≤ realPiA y := by
  exact_mod_cast piA_nonneg (encode y)

theorem realPiB_nonneg (y : SixY) : 0 ≤ realPiB y := by
  exact_mod_cast piB_nonneg (encode y)

theorem realPiA_normalized : (∑ y : SixY, realPiA y) = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  norm_num [realPiA, piA, encode, Fin.sum_univ_succ]

theorem realPiB_normalized : (∑ y : SixY, realPiB y) = 1 := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  norm_num [realPiB, piB, encode, Fin.sum_univ_succ]

/-- Support of the actual real coordinate vector stays inside the
proved graph-closed A communicating class. -/
theorem realPiA_supported :
    FiniteClosedSupport.IsSupportedReal realPiA classASet := by
  intro y hy
  have hnot : ¬ (encode y = (2 : Fin 6) ∨ encode y = (3 : Fin 6)) := hy
  simp [realPiA, piA, hnot]

theorem realPiB_supported :
    FiniteClosedSupport.IsSupportedReal realPiB classBSet := by
  intro y hy
  have hnot : ¬ (encode y = (4 : Fin 6) ∨ encode y = (5 : Fin 6)) := hy
  simp [realPiB, piB, hnot]

/-- The exact rational vector satisfies REAL stationarity for the
ACTUAL typed induced kernel, not merely the reference transition. -/
theorem realPiA_stationary (j : SixY) :
    pushVector (realTransition K) realPiA j = realPiA j := by
  rcases j with ⟨u, j⟩
  cases u
  unfold pushVector
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  change (∑ i : Fin 6, realPiA (decode i) *
      realTransition K (decode i) (decode j)) = realPiA (decode j)
  simp_rw [realTransition_typed_six_state]
  change (∑ i : Fin 6, ((piA i : ℚ) : ℝ) *
      ((transition i j : ℚ) : ℝ)) = ((piA j : ℚ) : ℝ)
  exact_mod_cast piA_stationary j

theorem realPiB_stationary (j : SixY) :
    pushVector (realTransition K) realPiB j = realPiB j := by
  rcases j with ⟨u, j⟩
  cases u
  unfold pushVector
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique]
  change (∑ i : Fin 6, realPiB (decode i) *
      realTransition K (decode i) (decode j)) = realPiB (decode j)
  simp_rw [realTransition_typed_six_state]
  change (∑ i : Fin 6, ((piB i : ℚ) : ℝ) *
      ((transition i j : ℚ) : ℝ)) = ((piB j : ℚ) : ℝ)
  exact_mod_cast piB_stationary j

/-- Fully normalized actual Markov probability measures built from the
explicit rational vectors, without redefining C2's abstract πA/πB. -/
noncomputable def explicitPiA : ProbabilityMeasure SixY :=
  ⟨vectorMeasure realPiA, vectorMeasure_isProbability realPiA
    realPiA_nonneg realPiA_normalized⟩

noncomputable def explicitPiB : ProbabilityMeasure SixY :=
  ⟨vectorMeasure realPiB, vectorMeasure_isProbability realPiB
    realPiB_nonneg realPiB_normalized⟩

theorem explicitPiA_spec :
    Kernel.Invariant K explicitPiA.toMeasure ∧
      explicitPiA.toMeasure classASet = 1 := by
  constructor
  · exact vectorMeasure_invariant K realPiA
      realPiA_nonneg realPiA_stationary
  · exact vectorMeasure_mass_one_of_support
      realPiA realPiA_nonneg realPiA_normalized classASet realPiA_supported

theorem explicitPiB_spec :
    Kernel.Invariant K explicitPiB.toMeasure ∧
      explicitPiB.toMeasure classBSet = 1 := by
  constructor
  · exact vectorMeasure_invariant K realPiB
      realPiB_nonneg realPiB_stationary
  · exact vectorMeasure_mass_one_of_support
      realPiB realPiB_nonneg realPiB_normalized classBSet realPiB_supported

/-- WHOLE probability-measure equality between the existing noncomputably
selected A stationary law and the explicit rational probability vector. -/
theorem piA_eq_explicit : ExactSixStateClassLaws.πA = explicitPiA := by
  obtain ⟨σ, hσ, hunique⟩ :=
    exists_unique_stationary_probability_on_class K
      classASet classASet_recurrent
  exact (hunique ExactSixStateClassLaws.πA πA_spec).trans
    (hunique explicitPiA explicitPiA_spec).symm

theorem piB_eq_explicit : ExactSixStateClassLaws.πB = explicitPiB := by
  obtain ⟨σ, hσ, hunique⟩ :=
    exists_unique_stationary_probability_on_class K
      classBSet classBSet_recurrent
  exact (hunique ExactSixStateClassLaws.πB πB_spec).trans
    (hunique explicitPiB explicitPiB_spec).symm

/-- All six actual typed A coordinates, not only a separately proved
rational matrix's candidate coefficients. -/
theorem piA_actual_singleton (j : Fin 6) :
    ExactSixStateClassLaws.πA.toMeasure ({decode j} : Set SixY) =
      ENNReal.ofReal ((piA j : ℚ) : ℝ) := by
  rw [piA_eq_explicit]
  change vectorMeasure realPiA {decode j} = _
  rw [vectorMeasure_singleton]
  simp [realPiA]

theorem piB_actual_singleton (j : Fin 6) :
    ExactSixStateClassLaws.πB.toMeasure ({decode j} : Set SixY) =
      ENNReal.ofReal ((piB j : ℚ) : ℝ) := by
  rw [piB_eq_explicit]
  change vectorMeasure realPiB {decode j} = _
  rw [vectorMeasure_singleton]
  simp [realPiB]

end ExactSixStateStationaryCoordinates
end MultipleLimit
end PermanssonResearch
