import PermanssonResearch.RegimeExit.CanonicalTailKernel
import PermanssonResearch.MultipleLimit.FiniteUniformAverage
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# C-Exit E (C70.1 ingredient) — deleting a finite prefix from an occupation law

For the frozen empirical occupation law
`ν̂_T^h(w) = T⁻¹ Σ_{t<T} δ_{h(w_t)}` (`RegimeSpecification.empiricalOccupation`)
and any bounded measurable test function `f` with `|f| ≤ C`, deleting the
first `k` observations changes the test integral by at most `2kC/(k+T)`:

  `|∫ f dν̂_{k+T}(w) − ∫ f dν̂_T(θ_k w)| ≤ 2 k C / (k + T)`.

This is the finite-prefix estimate behind random-entry occupation: it is
PROVED here, not asserted. Consequently weak convergence of the occupation
laws of the shifted path `θ_k w` implies weak convergence, to the same limit,
of the occupation laws of `w` itself (`tendsto_empiricalOccupation_of_tailShift`).

The descriptor is the declared global descriptor `h : Y → H`; observations
before the shift (for instance inside the source region before a regime
switch) are counted with that same global descriptor. Whether reading `h`
outside the target region is substantively meaningful is a separate
grounding question (v0.2.0 spec §9 item 2); this lemma is pure arithmetic.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ENNReal

namespace PermanssonResearch.RegimeExit

set_option autoImplicit false
open PermanssonLean PermanssonLean.RegimeSpecification

universe uS uX uH
variable {S : Type uS} {X : Type uX} {H : Type uH}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace H]

/-- Integral of a measurable real test function against the FROZEN
empirical occupation law is the arithmetic mean over `t = 0, …, T-1`, for an
arbitrary declared specification and arbitrary measurable `H`. -/
theorem integral_empiricalOccupation_eq_average
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) (T : ℕ) (hT : 0 < T)
    {f : H → ℝ} (hf : Measurable f) :
    ∫ x, f x ∂(empiricalOccupation spec w T hT : Measure H) =
      ((T : ℝ)⁻¹) * ∑ t ∈ Finset.range T, f (spec.descriptor (w t)) := by
  change ∫ x, f x ∂Measure.map
      (fun i : Fin T => spec.descriptor (w (i : ℕ)))
      (uniformFinProbability T hT).toMeasure = _
  rw [integral_map (measurable_of_finite _).aemeasurable hf.aestronglyMeasurable,
    MultipleLimit.FiniteUniformAverage.integral_uniformFin_eq_average T hT,
    Fin.sum_univ_eq_sum_range (fun t : ℕ => f (spec.descriptor (w t)))]

/-- Uniformly bounded arithmetic means are bounded by the same constant. -/
theorem abs_average_le
    (g : ℕ → ℝ) {C : ℝ} (hg : ∀ t, |g t| ≤ C) (T : ℕ) (hT : 0 < T) :
    |((T : ℝ)⁻¹) * ∑ t ∈ Finset.range T, g t| ≤ C := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hsum : |∑ t ∈ Finset.range T, g t| ≤ T * C := by
    calc
      |∑ t ∈ Finset.range T, g t| ≤ ∑ t ∈ Finset.range T, |g t| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range T, C := Finset.sum_le_sum fun t _ => hg t
      _ = T * C := by simp
  rw [abs_mul, abs_inv, abs_of_pos hTpos]
  rw [inv_mul_le_iff₀ hTpos]
  exact hsum

/-- **Finite-prefix estimate (arithmetic form).** Deleting the first `k`
terms of a sequence bounded by `C` changes its running mean at total length
`k + T` from the mean of the remaining `T` terms by at most `2kC/(k+T)`. -/
theorem abs_average_sub_shift_average_le
    (g : ℕ → ℝ) {C : ℝ} (hg : ∀ t, |g t| ≤ C) (k T : ℕ) (hT : 0 < T) :
    |((((k + T : ℕ) : ℝ))⁻¹) * ∑ t ∈ Finset.range (k + T), g t -
        ((T : ℝ)⁻¹) * ∑ t ∈ Finset.range T, g (k + t)| ≤
      2 * k * C / (k + T) := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hkT : (0 : ℝ) < k + T := by positivity
  set A := ∑ t ∈ Finset.range k, g t with hA
  set b := ((T : ℝ)⁻¹) * ∑ t ∈ Finset.range T, g (k + t) with hb
  have hsplit : ∑ t ∈ Finset.range (k + T), g t =
      A + ∑ t ∈ Finset.range T, g (k + t) := Finset.sum_range_add g k T
  have hB : ∑ t ∈ Finset.range T, g (k + t) = T * b := by
    rw [hb]; field_simp
  have hident :
      ((((k + T : ℕ) : ℝ))⁻¹) * ∑ t ∈ Finset.range (k + T), g t - b =
        (A - k * b) / (k + T) := by
    rw [hsplit, hB]; push_cast; field_simp; ring
  have hAbound : |A| ≤ k * C := by
    calc
      |A| ≤ ∑ t ∈ Finset.range k, |g t| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t ∈ Finset.range k, C := Finset.sum_le_sum fun t _ => hg t
      _ = k * C := by simp
  have hbbound : |b| ≤ C :=
    abs_average_le (fun t => g (k + t)) (fun t => hg (k + t)) T hT
  have hk0 : (0 : ℝ) ≤ k := by positivity
  rw [hident, abs_div, abs_of_pos hkT, div_le_div_iff_of_pos_right hkT]
  calc
    |A - k * b| ≤ |A| + |k * b| := abs_sub _ _
    _ = |A| + k * |b| := by rw [abs_mul, abs_of_nonneg hk0]
    _ ≤ k * C + k * C := add_le_add hAbound (mul_le_mul_of_nonneg_left hbbound hk0)
    _ = 2 * k * C := by ring

/-- **Finite-prefix estimate (occupation form).** For a bounded measurable
test function `|f| ≤ C`, the frozen occupation law of `w` at horizon `k+T`
and that of the shifted path `θ_k w` at horizon `T` have test integrals
within `2kC/(k+T)`. -/
theorem abs_integral_empiricalOccupation_sub_shift_le
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) (k T : ℕ) (hT : 0 < T)
    {f : H → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) :
    |∫ x, f x ∂(empiricalOccupation spec w (k + T)
          (Nat.add_pos_right k hT) : Measure H) -
        ∫ x, f x ∂(empiricalOccupation spec
          (pathTailShift (S := S) (X := X) k w) T hT : Measure H)| ≤
      2 * k * C / (k + T) := by
  rw [integral_empiricalOccupation_eq_average spec w (k + T) _ hf,
    integral_empiricalOccupation_eq_average spec _ T hT hf]
  exact abs_average_sub_shift_average_le
    (fun t => f (spec.descriptor (w t))) (fun t => hC _) k T hT

/-- **Prefix deletion preserves the weak occupation limit.** If the
occupation laws of the shifted path `θ_k w` converge weakly to `ν`, so do
the occupation laws of `w` itself. `k` is an arbitrary finite shift (for a
random entry time it is evaluated pathwise). -/
theorem tendsto_empiricalOccupation_of_tailShift
    [TopologicalSpace H] [OpensMeasurableSpace H]
    (spec : RegimeSpecification (JointState S X) H)
    (w : ℕ → JointState S X) (k : ℕ) {ν : ProbabilityMeasure H}
    (hshift : Tendsto (fun n : ℕ =>
        empiricalOccupation spec (pathTailShift (S := S) (X := X) k w)
          (n+1) (Nat.succ_pos n)) atTop (𝓝 ν)) :
    Tendsto (fun n : ℕ =>
        empiricalOccupation spec w (n+1) (Nat.succ_pos n)) atTop (𝓝 ν) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto] at hshift ⊢
  intro f
  have hf : Measurable (fun x => f x) := f.continuous.measurable
  have hC : ∀ x, |f x| ≤ ‖f‖ := fun x => by
    simpa [Real.norm_eq_abs] using f.norm_coe_le_norm x
  set g : ℕ → ℝ := fun t => f (spec.descriptor (w t)) with hg
  -- averages of the shifted path converge
  have hb : Tendsto (fun n : ℕ =>
      (((n+1 : ℕ) : ℝ)⁻¹) * ∑ t ∈ Finset.range (n+1), g (k + t))
        atTop (𝓝 (∫ x, f x ∂(ν : Measure H))) := by
    refine (hshift f).congr fun n => ?_
    rw [integral_empiricalOccupation_eq_average spec _ (n+1) _ hf]
    rfl
  -- the deletion error vanishes
  have herr : Tendsto (fun n : ℕ =>
      (((k + (n+1) : ℕ) : ℝ)⁻¹) * ∑ t ∈ Finset.range (k + (n+1)), g t -
        (((n+1 : ℕ) : ℝ)⁻¹) * ∑ t ∈ Finset.range (n+1), g (k + t))
        atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (a := fun n : ℕ => 2 * k * ‖f‖ / (k + (n + 1 : ℕ)))
    · intro n
      rw [Real.norm_eq_abs]
      have := abs_average_sub_shift_average_le g (fun t => hC _) k (n+1)
        (Nat.succ_pos n)
      simpa using this
    · have hden : Tendsto (fun n : ℕ => ((k + (n + 1 : ℕ) : ℕ) : ℝ))
          atTop atTop := by
        apply tendsto_natCast_atTop_atTop.comp
        exact tendsto_atTop_mono (fun n => (by show n ≤ k + (n + 1); omega)) tendsto_id
      have := (tendsto_const_nhds (x := 2 * (k : ℝ) * ‖f‖)).div_atTop hden
      simpa using this
  have hshifted : Tendsto (fun n : ℕ =>
      (((k + (n+1) : ℕ) : ℝ)⁻¹) * ∑ t ∈ Finset.range (k + (n+1)), g t)
        atTop (𝓝 (∫ x, f x ∂(ν : Measure H))) := by
    have := hb.add herr
    simpa using this
  rw [← tendsto_add_atTop_iff_nat k]
  refine hshifted.congr fun n => ?_
  rw [integral_empiricalOccupation_eq_average spec w _ _ hf]
  have hidx : n + k + 1 = k + (n + 1) := by omega
  simp only [hidx]
  rfl

end PermanssonResearch.RegimeExit
