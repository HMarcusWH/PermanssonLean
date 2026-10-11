import PermanssonResearch.MultipleLimit.FiniteInvariantUniqueness
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

/-!
# Lane C2 — uniqueness of a probability invariant law SUPPORTED ON A CLASS

A finite real stochastic matrix may have many global stationary laws.
Fixing a communicating class C and demanding that both stationary
probabilities be supported on C restores uniqueness.

The result has NO aperiodicity requirement and does not presuppose an
invariant distribution. Its assumptions describe exactly the *closed
class* support and mutual positive-edge reachability, and the proof
uses a minimal ratio within the finite subtype C.

Class-supported EXISTENCE is a separate theorem built using Cesaro
averages from an initial point inside C.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteClassInvariantUniqueness

open FiniteCesaroAlgebra
open FiniteInvariantUniqueness
open FiniteClosedSupport

variable {Y : Type*} [Fintype Y]
variable (K : Y → Y → ℝ) (hK : ∀ i j, 0 ≤ K i j)

/-- Stationarity and positive total mass force support positivity
at EVERY vertex of an irreducible class, as soon as the measure
is supported inside that class. -/
theorem strictly_positive_on_class
    (C : Set Y)
    (hcomm : ∀ i ∈ C, ∀ j ∈ C, Reachable K i j)
    (v : Y → ℝ)
    (hv : ∀ i, 0 ≤ v i)
    (hvtotal : (∑ i : Y, v i) = 1)
    (hvstat : ∀ j, pushVector K v j = v j)
    (hvsupp : IsSupportedReal v C) :
    ∀ j ∈ C, 0 < v j := by
  obtain ⟨i, hi⟩ := exists_positive_of_probability v hv hvtotal
  have hiC : i ∈ C := by
    by_contra hnot
    rw [hvsupp i hnot] at hi
    exact (lt_irrefl (0 : ℝ)) hi
  intro j hj
  exact positive_stationary_of_reachable K hK v hv hvstat hi
    (hcomm i hiC j hj)

/-- Two stationary real probability vectors supported on the SAME
finite irreducible class coincide globally, including zero outside
the class. No global irreducibility or uniqueness assumption. -/
theorem stationary_probability_unique_on_class
    (C : Set Y)
    (hcomm : ∀ i ∈ C, ∀ j ∈ C, Reachable K i j)
    (π σ : Y → ℝ)
    (hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 ≤ σ i)
    (hπtotal : (∑ i : Y, π i) = 1)
    (hσtotal : (∑ i : Y, σ i) = 1)
    (hπstat : ∀ j, pushVector K π j = π j)
    (hσstat : ∀ j, pushVector K σ j = σ j)
    (hπsupp : IsSupportedReal π C)
    (hσsupp : IsSupportedReal σ C) :
    π = σ := by
  classical
  have hσpos : ∀ i ∈ C, 0 < σ i :=
    strictly_positive_on_class K hK C hcomm σ hσ hσtotal hσstat hσsupp
  obtain ⟨i₀, hmin⟩ :=
    Finite.exists_min (fun i : {x : Y // x ∈ C} => π i.1 / σ i.1)
  let t : ℝ := π i₀.1 / σ i₀.1
  have htscale (i : Y) : t * σ i ≤ π i := by
    by_cases hiC : i ∈ C
    · have hdiv : t ≤ π i / σ i :=
        hmin ⟨i, hiC⟩
      exact (le_div_iff₀ (hσpos i hiC)).mp hdiv
    · rw [hπsupp i hiC, hσsupp i hiC, mul_zero]
  let τ : Y → ℝ := fun i => π i - t * σ i
  have hτnonneg : ∀ i : Y, 0 ≤ τ i := by
    intro i
    exact sub_nonneg.mpr (htscale i)
  have hτzero₀ : τ i₀.1 = 0 := by
    dsimp [τ, t]
    have hcancel : (π i₀.1 / σ i₀.1) * σ i₀.1 = π i₀.1 :=
      div_mul_cancel₀ _ (hσpos i₀.1 i₀.property).ne'
    rw [hcancel, sub_self]
  have hτstat : ∀ j, pushVector K τ j = τ j := by
    intro j
    calc
      pushVector K τ j =
          pushVector K π j - t * pushVector K σ j := by
        unfold pushVector τ
        simp_rw [sub_mul, Finset.sum_sub_distrib]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = τ j := by
        simp [τ, hπstat j, hσstat j]
  have hτzero : ∀ j : Y, τ j = 0 := by
    intro j
    by_cases hjC : j ∈ C
    · by_contra hjnot
      have hjpos : 0 < τ j :=
        lt_of_le_of_ne (hτnonneg j) (Ne.symm hjnot)
      have hpositive :=
        positive_stationary_of_reachable K hK τ hτnonneg hτstat
          hjpos (hcomm j hjC i₀.1 i₀.property)
      rw [hτzero₀] at hpositive
      exact (lt_irrefl (0 : ℝ)) hpositive
    · simp [τ, hπsupp j hjC, hσsupp j hjC]
  have hπscalar : ∀ i : Y, π i = t * σ i := by
    intro i
    have h := hτzero i
    dsimp [τ] at h
    linarith
  have hscale : (1 : ℝ) = t := by
    calc
      (1 : ℝ) = ∑ i : Y, π i := hπtotal.symm
      _ = ∑ i : Y, t * σ i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hπscalar i
      _ = t * (∑ i : Y, σ i) := by rw [Finset.mul_sum]
      _ = t := by rw [hσtotal, mul_one]
  funext i
  simpa only [← hscale, one_mul] using hπscalar i

end FiniteClassInvariantUniqueness
end MultipleLimit
end PermanssonResearch
