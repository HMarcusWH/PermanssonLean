import PermanssonResearch.MultipleLimit.TypedEndpointHitting
import Mathlib.Tactic

/-!
# Lane C1 — elementary cylinder-event/first-visit equivalence

Finite-horizon destination hitting is the literal event of visiting that
absorbing destination at some coordinate up to the horizon. The forbidden
set of each endpoint-specific target is empty. These pathwise identities
are needed before taking the increasing union to infinite time.
-/

open MeasureTheory ProbabilityTheory
namespace PermanssonResearch
namespace MultipleLimit
namespace TypedEndpointEvents

open TypedStrategicWitness TypedCanonicalHitting TypedEndpointHitting
open ExactEndpointRecurrences
open PermanssonResearch.ReverseSolver

theorem code_eq_a (z : Y) :
    codeState z = (2 : Fin 4) ↔ z = a := by
  rcases z with ⟨s, x⟩
  cases s <;> cases x <;> decide

theorem code_eq_b (z : Y) :
    codeState z = (3 : Fin 4) ↔ z = b := by
  rcases z with ⟨s, x⟩
  cases s <;> cases x <;> decide

theorem hitA_iff (T : ℕ) (w : ℕ → Y) :
    w ∈ hitA T ↔ ∃ n : ℕ, n ≤ T ∧ w n = a := by
  constructor
  · intro hw
    change (Preorder.frestrictLe T w) ∈
      successPrefixEvent (typedTarget aTarget) T at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    have hGoal : codeState (w (i : ℕ)) = (2 : Fin 4) := by
      simpa [typedTarget, rationalTargetAsFrozen, aTarget] using hi.1
    exact ⟨i, Finset.mem_Iic.mp i.property,
      (code_eq_a _).mp hGoal⟩
  · rintro ⟨n, hn, hw⟩
    change (Preorder.frestrictLe T w) ∈
      successPrefixEvent (typedTarget aTarget) T
    apply Set.mem_iUnion.mpr
    refine ⟨⟨n, Finset.mem_Iic.mpr hn⟩, ?_⟩
    constructor
    · change codeState (w n) ∈ (aTarget.goal : Set (Fin 4))
      simp [aTarget, hw, codeState, a]
    · apply Set.mem_iInter.mpr
      intro j
      simp [typedTarget, rationalTargetAsFrozen, aTarget]

theorem hitB_iff (T : ℕ) (w : ℕ → Y) :
    w ∈ hitB T ↔ ∃ n : ℕ, n ≤ T ∧ w n = b := by
  constructor
  · intro hw
    change (Preorder.frestrictLe T w) ∈
      successPrefixEvent (typedTarget bTarget) T at hw
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hw
    have hGoal : codeState (w (i : ℕ)) = (3 : Fin 4) := by
      simpa [typedTarget, rationalTargetAsFrozen, bTarget] using hi.1
    exact ⟨i, Finset.mem_Iic.mp i.property,
      (code_eq_b _).mp hGoal⟩
  · rintro ⟨n, hn, hw⟩
    change (Preorder.frestrictLe T w) ∈
      successPrefixEvent (typedTarget bTarget) T
    apply Set.mem_iUnion.mpr
    refine ⟨⟨n, Finset.mem_Iic.mpr hn⟩, ?_⟩
    constructor
    · change codeState (w n) ∈ (bTarget.goal : Set (Fin 4))
      simp [bTarget, hw, codeState, b]
    · apply Set.mem_iInter.mpr
      intro j
      simp [typedTarget, rationalTargetAsFrozen, bTarget]

theorem hitA_monotone : Monotone hitA := by
  intro m n hmn w hw
  obtain ⟨t, ht, hz⟩ := (hitA_iff m w).mp hw
  exact (hitA_iff n w).mpr ⟨t, ht.trans hmn, hz⟩

theorem hitB_monotone : Monotone hitB := by
  intro m n hmn w hw
  obtain ⟨t, ht, hz⟩ := (hitB_iff m w).mp hw
  exact (hitB_iff n w).mpr ⟨t, ht.trans hmn, hz⟩

theorem union_hitA :
    (⋃ T : ℕ, hitA T) = {w : ℕ → Y | ∃ n, w n = a} := by
  ext w
  constructor
  · intro hh
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hh
    obtain ⟨n, _, hn⟩ := (hitA_iff T w).mp hT
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n,
      (hitA_iff n w).mpr ⟨n, le_rfl, hn⟩⟩

theorem union_hitB :
    (⋃ T : ℕ, hitB T) = {w : ℕ → Y | ∃ n, w n = b} := by
  ext w
  constructor
  · intro hh
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hh
    obtain ⟨n, _, hn⟩ := (hitB_iff T w).mp hT
    exact ⟨n, hn⟩
  · rintro ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n,
      (hitB_iff n w).mpr ⟨n, le_rfl, hn⟩⟩

end TypedEndpointEvents
end MultipleLimit
end PermanssonResearch
