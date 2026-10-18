import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-! A fixed measurable descriptor of an actual natural-number clock.
Block k ends at (k+2)!, and has label k mod 2. Its last-block error
is at most 1/(k+2), giving distinct even/odd endpoint limits. -/

open Filter Finset
open scoped Topology
namespace PermanssonResearch.MultipleLimit.GrowingBlock
set_option autoImplicit false

theorem block_exists (n : ℕ) : ∃ k : ℕ, n < Nat.factorial (k+2) :=
  ⟨n,lt_of_lt_of_le (by omega) (Nat.self_le_factorial _)⟩

noncomputable def block (n : ℕ) : ℕ := Nat.find (block_exists n)

theorem block_eq {n k : ℕ} (hlo : Nat.factorial (k+1) ≤ n)
    (hhi : n < Nat.factorial (k+2)) : block n = k := by
  apply (Nat.find_eq_iff _).2
  refine ⟨hhi,?_⟩
  intro j hj
  exact not_lt.mpr ((Nat.factorial_le (by omega : j+2 ≤ k+1)).trans hlo)

def label (k : ℕ) : ℝ := (k % 2 : ℕ)
noncomputable def value (n : ℕ) : ℝ := label (block n)

theorem label_bounds (k : ℕ) : 0 ≤ label k ∧ label k ≤ 1 := by
  dsimp [label]
  constructor
  · positivity
  · exact_mod_cast (show k % 2 ≤ 1 from by omega)

theorem value_bounds (n : ℕ) : 0 ≤ value n ∧ value n ≤ 1 := label_bounds _

theorem difference_bound (n k : ℕ) : |value n-label k| ≤ 1 := by
  rcases value_bounds n with ⟨hv0,hv1⟩
  rcases label_bounds k with ⟨hl0,hl1⟩
  exact abs_le.mpr ⟨by linarith,by linarith⟩

noncomputable def average (T : ℕ) : ℝ := (∑ t ∈ range T, value t)/(T : ℝ)

theorem last_block_error (k : ℕ) :
    |average (Nat.factorial (k+2))-label k| ≤ 1/((k+2 : ℕ) : ℝ) := by
  let A := Nat.factorial (k+1)
  let N := Nat.factorial (k+2)
  have hAN : A ≤ N := Nat.factorial_le (by omega)
  have hN : 0 < (N : ℝ) := by dsimp [N]; positivity
  have hs : (∑ t ∈ range N, (value t-label k)) =
      ∑ t ∈ range A, (value t-label k) := by
    have he : N = A+(N-A) := (Nat.add_sub_of_le hAN).symm
    nth_rw 1 [he]
    rw [sum_range_add]
    have hz : (∑ i ∈ range (N-A), (value (A+i)-label k)) = 0 := by
      apply sum_eq_zero
      intro i hi
      have hbi : block (A+i) = k := block_eq (by dsimp [A]; omega)
        (by have := mem_range.mp hi; dsimp [N] at *; omega)
      simp only [value,hbi,sub_self]
    rw [hz,add_zero]
  have hp : |∑ t ∈ range A, (value t-label k)| ≤ (A : ℝ) := calc
    _ ≤ ∑ t ∈ range A, |value t-label k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _t ∈ range A, (1 : ℝ) := sum_le_sum fun t _ => difference_bound t k
    _ = (A : ℝ) := by simp
  have ha : average N-label k = (∑ t ∈ range N, (value t-label k))/(N : ℝ) := by
    rw [sum_sub_distrib]
    simp only [sum_const,card_range,nsmul_eq_mul,average]
    field_simp
  rw [ha,abs_div,abs_of_pos hN,hs]
  calc
    _ ≤ (A : ℝ)/(N : ℝ) := div_le_div_of_nonneg_right hp hN.le
    _ = 1/((k+2 : ℕ) : ℝ) := by
      have hR : (N : ℝ) = ((k+2 : ℕ) : ℝ)*(A : ℝ) := by
        dsimp [A,N]
        exact_mod_cast Nat.factorial_succ (k+1)
      have hF : (A : ℝ) ≠ 0 := by dsimp [A]; positivity
      rw [hR,div_mul_cancel_right₀ hF,one_div]

theorem endpoint_error_tendsto_zero :
    Tendsto (fun k => average (Nat.factorial (k+2))-label k) atTop (𝓝 0) := by
  apply squeeze_zero_norm (fun k => by simpa only [Real.norm_eq_abs] using last_block_error k)
  have ht := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 2)
  exact ht

theorem even_endpoints :
    Tendsto (fun k => average (Nat.factorial (2*k+2))) atTop (𝓝 0) := by
  have he : Tendsto (fun k : ℕ => 2*k) atTop atTop :=
    tendsto_atTop_mono (fun _ => by dsimp; omega) tendsto_id
  simpa [Function.comp_def,label,Nat.mul_mod] using endpoint_error_tendsto_zero.comp he

theorem odd_endpoints :
    Tendsto (fun k => average (Nat.factorial ((2*k+1)+2))) atTop (𝓝 1) := by
  have ho : Tendsto (fun k : ℕ => 2*k+1) atTop atTop :=
    tendsto_atTop_mono (fun _ => by dsimp; omega) tendsto_id
  have h := (endpoint_error_tendsto_zero.comp ho).add_const 1
  simpa [Function.comp_def,label,Nat.add_mod,Nat.mul_mod] using h

theorem averages_do_not_converge : ¬ ∃ a : ℝ, Tendsto average atTop (𝓝 a) := by
  rintro ⟨a,ha⟩
  have he : Tendsto (fun k : ℕ => Nat.factorial (2*k+2)) atTop atTop :=
    factorial_tendsto_atTop.comp (tendsto_atTop_mono (fun _ => by dsimp; omega) tendsto_id)
  have ho : Tendsto (fun k : ℕ => Nat.factorial ((2*k+1)+2)) atTop atTop :=
    factorial_tendsto_atTop.comp (tendsto_atTop_mono (fun _ => by dsimp; omega) tendsto_id)
  have h0 : a=0 := tendsto_nhds_unique (ha.comp he) even_endpoints
  have h1 : a=1 := tendsto_nhds_unique (ha.comp ho) odd_endpoints
  linarith

theorem positive_horizon_averages_do_not_converge :
    ¬ ∃ a : ℝ, Tendsto (fun n => average (n+1)) atTop (𝓝 a) := by
  rintro ⟨a,ha⟩
  exact averages_do_not_converge ⟨a,(tendsto_add_atTop_iff_nat 1).1 ha⟩

end PermanssonResearch.MultipleLimit.GrowingBlock
