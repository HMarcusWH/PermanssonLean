import PermanssonResearch.Probability.FiniteKantorovichDuality
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Explicit finite nearest-center quantizers for a separable metric space.
The first center is fixed, so the first moment itself dominates every error.
No finite approximation or measurable argmin theorem is assumed. -/

open MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace PermanssonResearch.Probability.FirstMomentQuantization
set_option autoImplicit false

variable {Y : Type*} [PseudoMetricSpace Y]

noncomputable def nearestIndex (u : ℕ → Y) : ℕ → Y → ℕ
  | 0, _ => 0
  | n+1, y => if dist y (u (n+1)) < dist y (u (nearestIndex u n y))
    then n+1 else nearestIndex u n y

theorem nearestIndex_le (u : ℕ → Y) (n : ℕ) (y : Y) : nearestIndex u n y ≤ n := by
  induction n with
  | zero => simp [nearestIndex]
  | succ n ih =>
    dsimp [nearestIndex]
    split_ifs <;> omega

theorem nearest_distance_le (u : ℕ → Y) (n : ℕ) (y : Y) (k : ℕ) (hk : k ≤ n) :
    dist y (u (nearestIndex u n y)) ≤ dist y (u k) := by
  induction n with
  | zero =>
    have hz : k = 0 := by omega
    subst k
    simp [nearestIndex]
  | succ n ih =>
    by_cases h : dist y (u (n+1)) < dist y (u (nearestIndex u n y))
    · rw [nearestIndex,if_pos h]
      by_cases he : k = n+1
      · subst k
        exact le_rfl
      · exact h.le.trans (ih (by omega))
    · rw [nearestIndex,if_neg h]
      by_cases he : k = n+1
      · subst k
        exact le_of_not_gt h
      · exact ih (by omega)

theorem nearest_error_tendsto (u : ℕ → Y) (hu : DenseRange u) (y : Y) :
    Tendsto (fun n => dist y (u (nearestIndex u n y))) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.2
  intro ε hε
  obtain ⟨k,hk⟩ := hu.exists_dist_lt y hε
  refine ⟨k,fun n hn => ?_⟩
  rw [Real.dist_eq,sub_zero,abs_of_nonneg dist_nonneg]
  exact (nearest_distance_le u n y k hn).trans_lt hk

variable [MeasurableSpace Y] [BorelSpace Y] [SeparableSpace Y]

theorem nearestIndex_measurable (u : ℕ → Y) (n : ℕ) : Measurable (nearestIndex u n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact Measurable.ite
      (measurableSet_lt (measurable_id.dist measurable_const)
        (measurable_id.dist ((measurable_of_countable u).comp ih))) measurable_const ih

def boundedIndex (n k : ℕ) : Fin (n+1) := ⟨min k n,Nat.lt_succ_of_le (Nat.min_le_right k n)⟩

noncomputable def finiteIndex (u : ℕ → Y) (n : ℕ) (y : Y) : Fin (n+1) :=
  boundedIndex n (nearestIndex u n y)

theorem finiteIndex_val (u : ℕ → Y) (n : ℕ) (y : Y) :
    (finiteIndex u n y).val = nearestIndex u n y :=
  Nat.min_eq_left (nearestIndex_le u n y)

theorem finiteIndex_measurable (u : ℕ → Y) (n : ℕ) : Measurable (finiteIndex u n) :=
  (measurable_of_countable (boundedIndex n)).comp (nearestIndex_measurable u n)

variable [Nonempty Y]

noncomputable def centers (y₀ : Y) : ℕ → Y
  | 0 => y₀
  | n+1 => denseSeq Y n

theorem centers_dense (y₀ : Y) : DenseRange (centers y₀) := by
  apply (denseRange_denseSeq Y).mono
  rintro y ⟨n,rfl⟩
  exact ⟨n+1,rfl⟩

noncomputable def center (y₀ : Y) (n : ℕ) (i : Fin (n+1)) : Y := centers y₀ i.val

noncomputable def quantizer (y₀ : Y) (n : ℕ) (y : Y) : Y :=
  center y₀ n (finiteIndex (centers y₀) n y)

theorem quantizer_eq_nearest (y₀ : Y) (n : ℕ) (y : Y) :
    quantizer y₀ n y = centers y₀ (nearestIndex (centers y₀) n y) := by
  simp only [quantizer,center,finiteIndex_val]

theorem quantizer_measurable (y₀ : Y) (n : ℕ) : Measurable (quantizer y₀ n) :=
  (measurable_of_finite (center y₀ n)).comp (finiteIndex_measurable (centers y₀) n)

noncomputable def error (y₀ : Y) (n : ℕ) (y : Y) : ℝ := dist y (quantizer y₀ n y)

theorem error_nonneg (y₀ : Y) (n : ℕ) (y : Y) : 0 ≤ error y₀ n y := dist_nonneg

theorem error_le_first_moment (y₀ : Y) (n : ℕ) (y : Y) : error y₀ n y ≤ dist y y₀ := by
  simpa [error,quantizer_eq_nearest,centers] using
    nearest_distance_le (centers y₀) n y 0 (Nat.zero_le n)

theorem error_measurable (y₀ : Y) (n : ℕ) : Measurable (error y₀ n) :=
  measurable_id.dist (quantizer_measurable y₀ n)

theorem error_tendsto (y₀ : Y) (y : Y) :
    Tendsto (fun n => error y₀ n y) atTop (𝓝 0) := by
  simpa [error,quantizer_eq_nearest] using
    nearest_error_tendsto (centers y₀) (centers_dense y₀) y

theorem error_integrable (μ : Measure Y) (y₀ : Y)
    (hμ : Integrable (fun y => dist y y₀) μ) (n : ℕ) : Integrable (error y₀ n) μ :=
  hμ.mono' (error_measurable y₀ n).aestronglyMeasurable
    (ae_of_all _ fun y => by
      simpa [Real.norm_eq_abs,abs_of_nonneg (error_nonneg y₀ n y)] using
        error_le_first_moment y₀ n y)

/-- Actual nearest-center errors converge in first moment by dominated
convergence for every law with a finite first moment. -/
theorem integral_error_tendsto (μ : Measure Y) (y₀ : Y)
    (hμ : Integrable (fun y => dist y y₀) μ) :
    Tendsto (fun n => ∫ y, error y₀ n y ∂μ) atTop (𝓝 0) := by
  simpa using tendsto_integral_of_dominated_convergence (μ := μ)
    (F := error y₀) (f := fun _ => (0 : ℝ)) (fun y => dist y y₀)
    (fun n => (error_measurable y₀ n).aestronglyMeasurable) hμ
    (fun n => ae_of_all _ fun y => by
      simpa [Real.norm_eq_abs,abs_of_nonneg (error_nonneg y₀ n y)] using
        error_le_first_moment y₀ n y)
    (ae_of_all _ fun y => error_tendsto y₀ y)

end PermanssonResearch.Probability.FirstMomentQuantization
