import PermanssonResearch.MultipleLimit.FiniteClassInvariantUniqueness
import PermanssonResearch.MultipleLimit.FiniteInvariantExistence
import Mathlib.Tactic

/-!
# Lane C2 — construct class-supported invariant probabilities, without assumptions

Fix a nonempty closed subset C of a real row-stochastic finite transition
matrix K. Redirect transitions FROM outside C to any chosen c∈C,
leaving all rows inside C unchanged.

The redirected finite stochastic matrix has a stationary probability
by the already constructed Cesaro compactness theorem. Every row of
the redirected matrix has ZERO mass going outside C, so stationary
balance forces the new probability to have zero support outside C.
Because its supported rows are unchanged, it is stationary for the
original matrix K as well.

For closed irreducible C, combine with the independent minimum-ratio
uniqueness result to construct exactly one supported invariant law.

This is a genuinely finite REAL statement; transport to an original
ENNReal Markov probability measure is handled separately.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteClassInvariantExistence

open FiniteCesaroAlgebra
open FiniteClosedSupport
open FiniteInvariantExistence
open FiniteClassInvariantUniqueness

variable {Y : Type*} [Fintype Y]
variable (K : Y → Y → ℝ)

/-- Stochastic surgery: outside C we jump immediately to a fixed
representative c∈C, but every original transition within C is kept. -/
noncomputable def redirectedMatrix (C : Set Y) (c : Y) (i j : Y) : ℝ := by
  classical
  exact if i ∈ C then K i j else if j = c then 1 else 0

theorem redirected_inside (C : Set Y) (c : Y)
    {i : Y} (hi : i ∈ C) (j : Y) :
    redirectedMatrix K C c i j = K i j := by
  classical
  simp [redirectedMatrix, hi]

theorem redirected_nonneg
    (hK : ∀ i j, 0 ≤ K i j)
    (C : Set Y) (c : Y) :
    ∀ i j, 0 ≤ redirectedMatrix K C c i j := by
  classical
  intro i j
  by_cases hi : i ∈ C
  · rw [redirected_inside K C c hi j]
    exact hK i j
  · simp only [redirectedMatrix, if_neg hi]
    split_ifs <;> norm_num

theorem redirected_row_sum
    (hrow : ∀ i : Y, ∑ j : Y, K i j = 1)
    (C : Set Y) (c : Y) :
    ∀ i : Y, ∑ j : Y, redirectedMatrix K C c i j = 1 := by
  classical
  intro i
  by_cases hi : i ∈ C
  · simpa only [redirected_inside K C c hi] using hrow i
  · simp [redirectedMatrix, hi]

theorem redirected_zero_outside
    (C : Set Y) (c : Y)
    (hc : c ∈ C)
    (hclosed : IsClosedReal K C)
    (i j : Y) (hj : j ∉ C) :
    redirectedMatrix K C c i j = 0 := by
  classical
  by_cases hi : i ∈ C
  · rw [redirected_inside K C c hi j]
    exact hclosed i hi j hj
  · have hjc : j ≠ c := by
      intro heq
      exact hj (heq.symm ▸ hc)
    simp [redirectedMatrix, hi, hjc]

/-- Every nonempty graph-closed set supports at least ONE
stationary probability vector for the original finite chain.
There is no irreducibility or periodicity hypothesis. -/
theorem exists_stationary_supported
    (hK : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i : Y, ∑ j : Y, K i j = 1)
    (C : Set Y) (c : Y) (hc : c ∈ C)
    (hclosed : IsClosedReal K C) :
    ∃ π : Y → ℝ,
      (∀ j, 0 ≤ π j) ∧
      (∑ j : Y, π j) = 1 ∧
      (∀ j, pushVector K π j = π j) ∧
      IsSupportedReal π C := by
  letI : Nonempty Y := ⟨c⟩
  obtain ⟨π, hπnonneg, hπmass, hπstat⟩ :=
    exists_stationary_real
      (redirectedMatrix K C c)
      (redirected_nonneg K hK C c)
      (redirected_row_sum K hrow C c)
  have hπsupport : IsSupportedReal π C := by
    intro j hj
    have hzero : ∀ i : Y, redirectedMatrix K C c i j = 0 :=
      fun i => redirected_zero_outside K C c hc hclosed i j hj
    have hpush : pushVector (redirectedMatrix K C c) π j = 0 := by
      unfold pushVector
      simp [hzero]
    exact (hπstat j).symm.trans hpush
  have hπorig (j : Y) : pushVector K π j = π j := by
    calc
      pushVector K π j =
          pushVector (redirectedMatrix K C c) π j := by
        unfold pushVector
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hiC : i ∈ C
        · rw [redirected_inside K C c hiC j]
        · rw [hπsupport i hiC]
          simp
      _ = π j := hπstat j
  exact ⟨π, hπnonneg, hπmass, hπorig, hπsupport⟩

/-- Existence AND uniqueness of stationary real probability supported on
a specified nonempty CLOSED IRREDUCIBLE class, without assuming either
statement or requiring convergence of its time marginals. -/
theorem exists_unique_stationary_on_class
    (hK : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i : Y, ∑ j : Y, K i j = 1)
    (C : Set Y) (c : Y) (hc : c ∈ C)
    (hclosed : IsClosedReal K C)
    (hcomm : ∀ i ∈ C, ∀ j ∈ C,
      FiniteInvariantUniqueness.Reachable K i j) :
    ∃! π : Y → ℝ,
      (∀ j, 0 ≤ π j) ∧
      (∑ j : Y, π j) = 1 ∧
      (∀ j, pushVector K π j = π j) ∧
      IsSupportedReal π C := by
  letI : Nonempty Y := ⟨c⟩
  obtain ⟨π, hnonneg, hmass, hstat, hsupp⟩ :=
    exists_stationary_supported K hK hrow C c hc hclosed
  refine ⟨π, ⟨hnonneg, hmass, hstat, hsupp⟩, ?_⟩
  intro σ hσ
  exact (stationary_probability_unique_on_class
    K hK C hcomm σ π
      hσ.1 hnonneg hσ.2.1 hmass
      hσ.2.2.1 hstat hσ.2.2.2 hsupp)

end FiniteClassInvariantExistence
end MultipleLimit
end PermanssonResearch
