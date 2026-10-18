import PermanssonResearch.Perturbation.ContractiveOccupation

/-!
# A-CONTRACT: a row test criterion for the existing global dual contraction

The exported conclusion is the existing all-probability-law predicate.  There
is no moment restriction and no appeal to coupling/dual equality.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal ProbabilityTheory

namespace PermanssonResearch.Perturbation

open PermanssonResearch.Probability

variable {Y : Type*} [PseudoMetricSpace Y] [MeasurableSpace Y]

/-- The bounded measurable image of a KR test under a Markov kernel. -/
theorem kr_kernel_image_bounded (K : Kernel Y Y) [IsMarkovKernel K]
    {f : Y → ℝ} (hf : IsKRTest f) :
    ∃ C, ∀ x, |∫ y, f y ∂K x| ≤ C := by
  obtain ⟨C, hC⟩ := hf.bounded
  refine ⟨C, fun x => ?_⟩
  have h := norm_integral_le_of_norm_le_const (μ := K x) (C := C) (f := f)
    (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
  simpa [Real.norm_eq_abs] using h

/-- Row contraction of every bounded measurable Lipschitz test implies the
original `IsW1Contraction`, including its zero-factor case. -/
theorem isW1Contraction_of_test_images
    (K : Kernel Y Y) [IsMarkovKernel K] {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hrows : ∀ f : Y → ℝ, IsKRTest f → ∀ x y,
      |∫ z, f z ∂K x - ∫ z, f z ∂K y| ≤ ρ * dist x y) :
    IsW1Contraction K ρ := by
  intro μ ν hμ hν c hc f hf
  let : IsProbabilityMeasure μ := hμ
  let : IsProbabilityMeasure ν := hν
  let F : Y → ℝ := fun x => ∫ y, f y ∂K x
  have hFm : Measurable F :=
    hf.measurable.stronglyMeasurable.integral_kernel.measurable
  obtain ⟨C, hC⟩ := kr_kernel_image_bounded K hf
  have hFI (θ : Measure Y) [IsProbabilityMeasure θ] : Integrable F θ :=
    Integrable.of_bound hFm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
  have hcomp (θ : Measure Y) [IsProbabilityMeasure θ] :
      ∫ y, f y ∂(K ∘ₘ θ) = ∫ x, F x ∂θ := by
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp]
    · rfl
    · rw [← Measure.comp_eq_comp_const_apply]
      exact hf.integrable _
  rw [hcomp μ, hcomp ν]
  rcases eq_or_lt_of_le hρ with hzero | hpos
  · have hconst : ∀ x y, F x = F y := by
      intro x y
      have h := hrows f hf x y
      rw [← hzero, zero_mul] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    have hne : Nonempty Y := by
      by_contra hn
      rw [not_nonempty_iff] at hn
      have h := measure_univ (μ := μ)
      simp [Set.univ_eq_empty_iff.mpr hn] at h
    obtain ⟨x₀⟩ := hne
    simp only [hconst _ x₀, integral_const, probReal_univ, one_smul,
      sub_self, abs_zero, ← hzero, zero_mul, le_refl]
  · let g : Y → ℝ := fun x => ρ⁻¹ * F x
    have hg : IsKRTest g := by
      refine ⟨measurable_const.mul hFm, ?_, ?_⟩
      · refine LipschitzWith.of_dist_le_mul fun x y => ?_
        change dist (ρ⁻¹ * F x) (ρ⁻¹ * F y) ≤ _
        rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hpos)]
        calc ρ⁻¹ * |F x - F y| ≤ ρ⁻¹ * (ρ * dist x y) :=
            mul_le_mul_of_nonneg_left (hrows f hf x y) (inv_nonneg.mpr hρ)
          _ = ((1 : ℝ≥0) : ℝ) * dist x y := by
            rw [inv_mul_cancel_left₀ hpos.ne']; simp
      · refine ⟨ρ⁻¹ * C, fun x => ?_⟩
        change |ρ⁻¹ * F x| ≤ _
        rw [abs_mul, abs_of_pos (inv_pos.mpr hpos)]
        exact mul_le_mul_of_nonneg_left (hC x) (inv_nonneg.mpr hρ)
    have h := hc g hg
    simp only [g, integral_const_mul, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.mpr hpos)] at h
    exact (inv_mul_le_iff₀ hpos).mp h

/-- A genuinely normalized refresh kernel supplies a strict contraction
certificate with factor zero, rather than a renamed contraction hypothesis. -/
theorem constantKernel_isW1Contraction (π : Measure Y) [IsProbabilityMeasure π] :
    IsW1Contraction (Kernel.const Y π) 0 := by
  apply isW1Contraction_of_test_images _ le_rfl
  intro f hf x y
  simp

/-- The identity kernel is nonexpansive. It need not be strictly contractive. -/
theorem identityKernel_isW1Contraction : IsW1Contraction (Kernel.id : Kernel Y Y) 1 := by
  apply isW1Contraction_of_test_images _ zero_le_one
  intro f hf x y
  rw [Kernel.id_apply, Kernel.id_apply,
    integral_dirac' f x hf.measurable.stronglyMeasurable,
    integral_dirac' f y hf.measurable.stronglyMeasurable]
  simpa [Real.dist_eq] using hf.lipschitz.dist_le_mul x y

end PermanssonResearch.Perturbation
