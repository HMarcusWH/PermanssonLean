import PermanssonResearch.MultipleLimit.FiniteInvariantExistence
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic

/-!
# Lane C2 — uniqueness of invariant real probabilities under irreducibility

For arbitrary (possibly irrational) finite row-stochastic REAL matrices,
if every state is positive-edge reachable from every other state then
the normalized invariant row vector is unique. There is NO aperiodicity
condition and NO assumption of uniqueness in the theorem hypotheses.

The proof uses the minimal ratio π_i/σ_i, a nonnegative stationary
difference τ = π - tσ with one zero coordinate, and positivity
propagation along strong-connectivity paths to show τ vanishes.
Existence is separately proved by Cesaro compactness.

A verified real stochastic matrix theorem is NOT YET a theorem about
ENNReal-valued Markov kernels until the exact atom-to-real bridge is proved.
-/

namespace PermanssonResearch
namespace MultipleLimit
namespace FiniteInvariantUniqueness

open FiniteCesaroAlgebra

variable {Y : Type*} [Fintype Y] [Nonempty Y]
variable (K : Y → Y → ℝ) (hK : ∀ i j, 0 ≤ K i j)

def PositiveEdge (i j : Y) : Prop := 0 < K i j
def Reachable (i j : Y) : Prop :=
  Relation.ReflTransGen (PositiveEdge K) i j

/-- A positive coordinate of a nonnegative stationary vector sends
strict positive mass along each positive-probability outgoing edge. -/
theorem positive_stationary_of_edge
    (hK : ∀ i j, 0 ≤ K i j)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hstat : ∀ j, pushVector K v j = v j)
    {i j : Y}
    (hi : 0 < v i) (hij : PositiveEdge K i j) :
    0 < v j := by
  have hsum : v i * K i j ≤ pushVector K v j := by
    unfold pushVector
    exact Finset.single_le_sum
      (fun z hz => mul_nonneg (hv z) (hK z j))
      (Finset.mem_univ i)
  exact lt_of_lt_of_le (mul_pos hi hij) (hsum.trans_eq (hstat j))

theorem positive_stationary_of_reachable
    (hK : ∀ i j, 0 ≤ K i j)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hstat : ∀ j, pushVector K v j = v j)
    {i j : Y}
    (hi : 0 < v i) (hij : Reachable K i j) :
    0 < v j := by
  induction hij with
  | refl => exact hi
  | tail hab hbc ih =>
      exact positive_stationary_of_edge K hK v hv hstat ih hbc

/-- A nonnegative finite row vector with mass one has some strictly
positive component. -/
theorem exists_positive_of_probability
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hvtotal : (∑ i : Y, v i) = 1) :
    ∃ i : Y, 0 < v i := by
  by_contra hnone
  push_neg at hnone
  have hz : ∀ i : Y, v i = 0 :=
    fun i => le_antisymm (hnone i) (hv i)
  have hs : (∑ i : Y, v i) = 0 := by
    simp [hz]
  linarith

theorem positive_everywhere_of_irreducible
    (hK : ∀ i j, 0 ≤ K i j)
    (v : Y → ℝ) (hv : ∀ i, 0 ≤ v i)
    (hvtotal : (∑ i : Y, v i) = 1)
    (hstat : ∀ j, pushVector K v j = v j)
    (hirr : ∀ i j : Y, Reachable K i j) :
    ∀ j, 0 < v j := by
  obtain ⟨i, hi⟩ := exists_positive_of_probability v hv hvtotal
  exact fun j => positive_stationary_of_reachable K hK v hv hstat hi (hirr i j)

/-- Every nonempty finite irreducible real stochastic matrix has AT
MOST ONE invariant probability vector. This is NOT merely uniqueness
conditional on a supplied ratio/ergodic hypothesis. -/
theorem stationary_probability_unique
    (hK : ∀ i j, 0 ≤ K i j)
    (hirr : ∀ i j : Y, Reachable K i j)
    (π σ : Y → ℝ)
    (hπ : ∀ i, 0 ≤ π i)
    (hσ : ∀ i, 0 ≤ σ i)
    (hπtotal : (∑ i : Y, π i) = 1)
    (hσtotal : (∑ i : Y, σ i) = 1)
    (hπstat : ∀ j, pushVector K π j = π j)
    (hσstat : ∀ j, pushVector K σ j = σ j) :
    π = σ := by
  classical
  have hσpos : ∀ i : Y, 0 < σ i :=
    positive_everywhere_of_irreducible K hK σ hσ hσtotal hσstat hirr
  obtain ⟨i₀, hmin⟩ :=
    Finite.exists_min (fun i : Y => π i / σ i)
  let t : ℝ := π i₀ / σ i₀
  have htscale (i : Y) : t * σ i ≤ π i := by
    exact (le_div_iff₀ (hσpos i)).mp (hmin i)
  let τ : Y → ℝ := fun i => π i - t * σ i
  have hτnonneg : ∀ i : Y, 0 ≤ τ i := by
    intro i
    dsimp [τ]
    exact sub_nonneg.mpr (htscale i)
  have hτzero₀ : τ i₀ = 0 := by
    dsimp [τ, t]
    have hcancel : (π i₀ / σ i₀) * σ i₀ = π i₀ :=
      div_mul_cancel₀ _ (hσpos i₀).ne'
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
    by_contra hj
    have hjpos : 0 < τ j :=
      lt_of_le_of_ne (hτnonneg j) (Ne.symm hj)
    have hpositive :=
      positive_stationary_of_reachable K hK τ hτnonneg hτstat
        hjpos (hirr j i₀)
    rw [hτzero₀] at hpositive
    exact (lt_irrefl (0 : ℝ)) hpositive
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

/-- Combine the already constructed stationary real distribution and
the new irreducible uniqueness proof. This theorem assumes only the
real stochastic rows and positive-edge graph irreducibility. -/
theorem exists_unique_stationary_real
    (hK : ∀ i j, 0 ≤ K i j)
    (hrow : ∀ i, ∑ j : Y, K i j = 1)
    (hirr : ∀ i j : Y, Reachable K i j) :
    ∃! π : Y → ℝ,
      (∀ j, 0 ≤ π j) ∧
      (∑ j : Y, π j) = 1 ∧
      ∀ j, pushVector K π j = π j := by
  obtain ⟨π, hπ, hπtotal, hπstat⟩ :=
    FiniteInvariantExistence.exists_stationary_real K hK hrow
  refine ⟨π, ⟨hπ, hπtotal, hπstat⟩, ?_⟩
  intro σ hσ
  exact (stationary_probability_unique K hK hirr
    σ π hσ.1 hπ hσ.2.1 hπtotal hσ.2.2 hπstat).symm

end FiniteInvariantUniqueness
end MultipleLimit
end PermanssonResearch
