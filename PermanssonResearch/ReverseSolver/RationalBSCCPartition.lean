import PermanssonResearch.ReverseSolver.RationalBSCCNative
import PermanssonResearch.ReverseSolver.RationalRecurrentAccess
import Mathlib.Tactic

/-!
# C10 — partition of the computed recurrent union by bottom classes

Computed rational BSCCs are pairwise disjoint and cover exactly their
recurrent union. The proof transports them to C2's *actual* typed
canonical recurrent-class partition; no unchecked state ordering or
arbitrary baseline class selector enters the result.
-/

namespace PermanssonResearch
namespace ReverseSolver
namespace C10

set_option autoImplicit false

open PermanssonResearch.MultipleLimit.RecurrentClassDecomposition
open FiniteStrategicRealization

/-- Distinct exact computed bottom classes share no physical state. -/
theorem bottomClasses_common_member_eq {n : ℕ}
    (L : RationalMarkovMatrix n)
    (C D : Finset (Fin n))
    (hC : C ∈ bottomClasses L) (hD : D ∈ bottomClasses L)
    (x : Fin n) (hxC : x ∈ C) (hxD : x ∈ D) :
    C = D := by
  let K := (rationalStrategicIntervention L L).intervention.apply.inducedKernel
  have hCN : decodedClass C ∈ RecurrentClasses K :=
    (bottomClasses_native_iff L L C).mp hC
  have hDN : decodedClass D ∈ RecurrentClasses K :=
    (bottomClasses_native_iff L L D).mp hD
  by_contra hne
  have hneN : decodedClass C ≠ decodedClass D := by
    intro heq
    exact hne (decodedClass_injective heq)
  have hdisjoint := recurrentClasses_disjoint_of_ne K hCN hDN hneN
  have hxCN : decode x ∈ decodedClass C := by
    simpa [decodedClass] using hxC
  have hxDN : decode x ∈ decodedClass D := by
    simpa [decodedClass] using hxD
  exact (Set.disjoint_left.mp hdisjoint) hxCN hxDN

/-- Every truly recurrent state belongs to EXACTLY ONE of the computed
bottom classes: its class-indicator partition sums to one over ℚ. -/
theorem bottomClasses_indicator_sum_one {n : ℕ}
    (L : RationalMarkovMatrix n) (x : Fin n)
    (hx : x ∈ rationalRecurrentUnion L) :
    (∑ C ∈ bottomClasses L, if x ∈ C then (1 : ℚ) else 0) = 1 := by
  obtain ⟨C, hC, hxC⟩ := (Finset.mem_biUnion).mp hx
  have hpoint (D : Finset (Fin n)) (hD : D ∈ bottomClasses L) :
      (if x ∈ D then (1 : ℚ) else 0) =
        (if D = C then 1 else 0) := by
    by_cases hxD : x ∈ D
    · have hEq : D = C :=
        (bottomClasses_common_member_eq L D C hD hC x hxD hxC)
      subst D
      simp [hxC]
    · have hNe : D ≠ C := by
        intro hEq
        subst D
        exact hxD hxC
      simp [hxD, hNe]
  calc
    (∑ D ∈ bottomClasses L, if x ∈ D then (1 : ℚ) else 0) =
      (∑ D ∈ bottomClasses L, if D = C then (1 : ℚ) else 0) := by
        apply Finset.sum_congr rfl
        intro D hD
        exact hpoint D hD
    _ = 1 := by simp [hC]

end C10
end ReverseSolver
end PermanssonResearch