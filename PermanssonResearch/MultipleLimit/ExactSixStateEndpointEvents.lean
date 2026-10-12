import PermanssonResearch.MultipleLimit.ExactSixStateEndpointRecurrences
import PermanssonResearch.MultipleLimit.ExactSixStateTyped
import PermanssonResearch.MultipleLimit.FiniteCanonicalPath
import Mathlib.Tactic

/-!
# C53-13 — true infinite typed six-state path, finite class-hit cylinders

The rational class-specific A/B hitting recurrences are now transported
through the exact finite-prefix marginal of the genuine typed alpha/P/U
infinite path law, with fully explicit time-zero-inclusive events.
No artificial process or independence assumption is introduced.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace ExactSixStateEndpointEvents

open PermanssonLean
open ReverseSolver
open ReverseSolver.FiniteStrategicPathBridge
open ReverseSolver.FiniteStrategicRealization
open FiniteCanonicalPath
open ExactSixState
open ExactSixStateCanonical
open ExactSixStateTyped
open ExactSixStateEndpointRecurrences

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

def hitA (T : ℕ) : Set (ℕ → JointState Unit (Fin 6)) :=
  (Preorder.frestrictLe T) ⁻¹'
    successPrefixEvent (typedTarget targetA) T

def hitB (T : ℕ) : Set (ℕ → JointState Unit (Fin 6)) :=
  (Preorder.frestrictLe T) ⁻¹'
    successPrefixEvent (typedTarget targetB) T

theorem hitA_measurable (T : ℕ) : MeasurableSet (hitA T) :=
  (measurableSet_successPrefixEvent (typedTarget targetA) T).preimage
    (Preorder.measurable_frestrictLe T)

theorem hitB_measurable (T : ℕ) : MeasurableSet (hitB T) :=
  (measurableSet_successPrefixEvent (typedTarget targetB) T).preimage
    (Preorder.measurable_frestrictLe T)

/-- Exact pointwise finite-history event: class A is observed
at some time through T; its two physical members are both valid hits. -/
theorem hitA_iff (T : ℕ) (w : ℕ → JointState Unit (Fin 6)) :
    w ∈ hitA T ↔ ∃ n : ℕ, n ≤ T ∧ encode (w n) ∈ classA := by
  constructor
  · intro hw
    change (Preorder.frestrictLe T w) ∈
      successPrefixEvent (typedTarget targetA) T at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    have hGoal : encode (w (i : ℕ)) ∈ classA := by
      simpa [typedTarget, rationalTargetAsFrozen,
        targetA, classA] using hi.1
    exact ⟨i, Finset.mem_Iic.mp i.property, hGoal⟩
  · rintro ⟨n, hn, hw⟩
    change (Preorder.frestrictLe T w) ∈
      successPrefixEvent (typedTarget targetA) T
    apply Set.mem_iUnion.mpr
    refine ⟨⟨n, Finset.mem_Iic.mpr hn⟩, ?_⟩
    constructor
    · change encode (w n) ∈ (targetA.goal : Set (Fin 6))
      simpa [targetA, classA] using hw
    · apply Set.mem_iInter.mpr
      intro j
      simp [typedTarget, rationalTargetAsFrozen, targetA]

theorem hitB_iff (T : ℕ) (w : ℕ → JointState Unit (Fin 6)) :
    w ∈ hitB T ↔ ∃ n : ℕ, n ≤ T ∧ encode (w n) ∈ classB := by
  constructor
  · intro hw
    change (Preorder.frestrictLe T w) ∈
      successPrefixEvent (typedTarget targetB) T at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    have hGoal : encode (w (i : ℕ)) ∈ classB := by
      simpa [typedTarget, rationalTargetAsFrozen,
        targetB, classB] using hi.1
    exact ⟨i, Finset.mem_Iic.mp i.property, hGoal⟩
  · rintro ⟨n, hn, hw⟩
    change (Preorder.frestrictLe T w) ∈
      successPrefixEvent (typedTarget targetB) T
    apply Set.mem_iUnion.mpr
    refine ⟨⟨n, Finset.mem_Iic.mpr hn⟩, ?_⟩
    constructor
    · change encode (w n) ∈ (targetB.goal : Set (Fin 6))
      simpa [targetB, classB] using hw
    · apply Set.mem_iInter.mpr
      intro j
      simp [typedTarget, rationalTargetAsFrozen, targetB]

theorem hitA_monotone : Monotone hitA := by
  intro m n hmn w hw
  obtain ⟨t, ht, hz⟩ := (hitA_iff m w).mp hw
  exact (hitA_iff n w).mpr ⟨t, ht.trans hmn, hz⟩

theorem hitB_monotone : Monotone hitB := by
  intro m n hmn w hw
  obtain ⟨t, ht, hz⟩ := (hitB_iff m w).mp hw
  exact (hitB_iff n w).mpr ⟨t, ht.trans hmn, hz⟩

theorem union_hitA :
    (⋃ T : ℕ, hitA T) =
      {w : ℕ → JointState Unit (Fin 6) |
        ∃ n : ℕ, encode (w n) ∈ classA} := by
  ext w
  constructor
  · rintro ⟨T,hT⟩
    obtain ⟨n,_,hn⟩ := (hitA_iff T w).mp hT
    exact ⟨n,hn⟩
  · rintro ⟨n,hn⟩
    exact Set.mem_iUnion.mpr
      ⟨n,(hitA_iff n w).mpr ⟨n, le_rfl, hn⟩⟩

theorem union_hitB :
    (⋃ T : ℕ, hitB T) =
      {w : ℕ → JointState Unit (Fin 6) |
        ∃ n : ℕ, encode (w n) ∈ classB} := by
  ext w
  constructor
  · rintro ⟨T,hT⟩
    obtain ⟨n,_,hn⟩ := (hitB_iff T w).mp hT
    exact ⟨n,hn⟩
  · rintro ⟨n,hn⟩
    exact Set.mem_iUnion.mpr
      ⟨n,(hitB_iff n w).mpr ⟨n, le_rfl, hn⟩⟩

/-- Direct finite-prefix transport from the typed alpha/P/U
Ionescu–Tulcea infinite path law. This is not a finite simulated word. -/
theorem typed_hitA_real (i : Fin 6) (T : ℕ) :
    (typedModel.pathLaw (Measure.dirac (decode i))).real (hitA T) =
      (rationalHittingValue sixStateMatrix targetA T i : ℝ) := by
  have hprefix :
      (typedModel.pathLaw (Measure.dirac (decode i))).map
        (Preorder.frestrictLe T) =
      PermanssonLean.ProbabilitySupport.finitePrefixLaw
        typedModel.inducedKernel (decode i) T := by
    rw [FiniteCanonicalPath.typed_pathLaw_eq_canonical]
    exact FiniteCanonicalPath.canonicalPathLaw_prefix_dirac
      typedModel.inducedKernel (decode i) T
  unfold hitA
  unfold Measure.real
  rw [← Measure.map_apply (Preorder.measurable_frestrictLe T)
    (measurableSet_successPrefixEvent (typedTarget targetA) T)]
  rw [hprefix]
  exact typed_hitting_all_horizons i T

theorem typed_hitB_real (i : Fin 6) (T : ℕ) :
    (typedModel.pathLaw (Measure.dirac (decode i))).real (hitB T) =
      (rationalHittingValue sixStateMatrix targetB T i : ℝ) := by
  have hprefix :
      (typedModel.pathLaw (Measure.dirac (decode i))).map
        (Preorder.frestrictLe T) =
      PermanssonLean.ProbabilitySupport.finitePrefixLaw
        typedModel.inducedKernel (decode i) T := by
    rw [FiniteCanonicalPath.typed_pathLaw_eq_canonical]
    exact FiniteCanonicalPath.canonicalPathLaw_prefix_dirac
      typedModel.inducedKernel (decode i) T
  unfold hitB
  unfold Measure.real
  rw [← Measure.map_apply (Preorder.measurable_frestrictLe T)
    (measurableSet_successPrefixEvent (typedTarget targetB) T)]
  rw [hprefix]
  exact typed_hitting_all_horizons i T

end
end ExactSixStateEndpointEvents
end MultipleLimit
end PermanssonResearch
