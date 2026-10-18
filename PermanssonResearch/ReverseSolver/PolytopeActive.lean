import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Tactic

/-!
# Actual active constraints at a finite polytope vertex

The active rows have zero common kernel.  The proof constructs both directions
of a feasible line if a nonzero common-kernel vector existed.  No vertex or
linear-program completeness certificate is assumed.
-/

namespace PermanssonResearch.ReverseSolver.ExactPolytope

open Set Filter Matrix
open scoped Topology

variable {I J : Type*} [Fintype I] [Fintype J]

def feasible (A : Matrix I J ℝ) (b : I → ℝ) : Set (J → ℝ) :=
  {x | ∀ i, dotProduct (A i) x ≤ b i}

theorem feasible_isClosed (A : Matrix I J ℝ) (b : I → ℝ) :
    IsClosed (feasible A b) := by
  have he : feasible A b = ⋂ i, {x | dotProduct (A i) x ≤ b i} := by
    ext x
    simp [feasible]
  rw [he]
  exact isClosed_iInter fun i => isClosed_le (by unfold dotProduct; fun_prop) continuous_const

theorem feasible_convex (A : Matrix I J ℝ) (b : I → ℝ) :
    Convex ℝ (feasible A b) := by
  intro x hx y hy a c ha hc hac i
  simp only [dotProduct, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_add, mul_left_comm (A i _) a, mul_left_comm (A i _) c]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  calc
    _ ≤ a * b i + c * b i := add_le_add (mul_le_mul_of_nonneg_left (hx i) ha)
      (mul_le_mul_of_nonneg_left (hy i) hc)
    _ = b i := by rw [← add_mul, hac, one_mul]

theorem feasible_line_near_zero (A : Matrix I J ℝ) (b : I → ℝ)
    (x : J → ℝ) (hx : x ∈ feasible A b) (z : J → ℝ)
    (hz : ∀ i, dotProduct (A i) x = b i → dotProduct (A i) z = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • z ∈ feasible A b := by
  classical
  change ∀ᶠ t : ℝ in 𝓝 0, ∀ i, dotProduct (A i) (x + t • z) ≤ b i
  rw [Filter.eventually_all]
  intro i
  by_cases hi : dotProduct (A i) x = b i
  · filter_upwards [] with t
    simp [dotProduct_add, dotProduct_smul, hz i hi, hi]
  · have hlt : dotProduct (A i) x < b i := lt_of_le_of_ne (hx i) hi
    have hcont : Continuous (fun t : ℝ => dotProduct (A i) (x + t • z)) := by
      unfold dotProduct
      fun_prop
    exact (hcont.continuousAt.eventually (gt_mem_nhds (by simpa using hlt))).mono
      fun _ ht => ht.le

theorem extreme_active_kernel_zero (A : Matrix I J ℝ) (b : I → ℝ)
    (x : J → ℝ) (hx : x ∈ (feasible A b).extremePoints ℝ)
    (z : J → ℝ)
    (hz : ∀ i, dotProduct (A i) x = b i → dotProduct (A i) z = 0) : z = 0 := by
  obtain ⟨ε, hε, he⟩ := Metric.eventually_nhds_iff.mp
    (feasible_line_near_zero A b x hx.1 z hz)
  have hplus : x + (ε / 2) • z ∈ feasible A b :=
    he (by rw [Real.dist_eq]; simp only [sub_zero, abs_of_pos (half_pos hε)]; linarith)
  have hminus : x - (ε / 2) • z ∈ feasible A b := by
    have ht := he (y := -(ε / 2)) (by
      rw [Real.dist_eq]; simp only [sub_zero, abs_neg, abs_of_pos (half_pos hε)]; linarith)
    simpa only [neg_smul, sub_eq_add_neg] using ht
  have heq := hx.2 hplus hminus (mem_openSegment_add_sub (𝕜 := ℝ) x ((ε / 2) • z))
  have hzero : (ε / 2) • z = 0 := (add_eq_left.mp heq)
  exact (smul_eq_zero.mp hzero).resolve_left (ne_of_gt (half_pos hε))

/-- A linear objective on a nonempty compact polytope attains at a vertex. -/
theorem compact_exists_optimal_vertex (A : Matrix I J ℝ) (b : I → ℝ)
    (hc : IsCompact (feasible A b)) (hn : (feasible A b).Nonempty)
    (objective : (J → ℝ) →L[ℝ] ℝ) :
    ∃ x ∈ (feasible A b).extremePoints ℝ,
      ∀ y ∈ feasible A b, objective y ≤ objective x := by
  let F := {x ∈ feasible A b | ∀ y ∈ feasible A b, objective y ≤ objective x}
  have hf : IsExposed ℝ (feasible A b) F := fun _ => ⟨objective, rfl⟩
  obtain ⟨x, hx, hm⟩ := hc.exists_isMaxOn hn objective.continuous.continuousOn
  obtain ⟨v, hv⟩ := (hf.isCompact hc).extremePoints_nonempty ⟨x, hx, hm⟩
  exact ⟨v, hf.isExtreme.extremePoints_subset_extremePoints hv, hv.1.2⟩

end PermanssonResearch.ReverseSolver.ExactPolytope
