import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.MetricSpace.Lipschitz

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory


/-!
# A3.0 — Wasserstein-1 in Kantorovich–Rubinstein dual form

`W1DualLE μ ν c` states that every measurable, bounded, 1-Lipschitz test function
has integrals under `μ` and `ν` within `c`. It is stated on an ARBITRARY
pseudo-metric space with an arbitrary σ-algebra (no Polish / standard-Borel /
countability hypothesis); measurability is part of the test class. Equality with
the coupling definition of `W₁` (Kantorovich–Rubinstein duality) is NOT
formalized; every A3 statement is about this dual-form bound.

Calculus: monotonicity, symmetry, triangle, closure under limits, the mixture of
pointwise kernel defects (`W1DualLE.comp_of_forall`), pushforward by an
`L`-Lipschitz measurable map (`W1DualLE.map_lipschitz`), and a finite bound from
first moments (`W1DualLE.of_integrable_dist`).
-/

namespace PermanssonResearch.Probability

set_option autoImplicit false

universe uY uV
variable {Y : Type uY} [PseudoMetricSpace Y] [MeasurableSpace Y]

/-- Kantorovich–Rubinstein test functions: measurable, bounded, 1-Lipschitz. -/
structure IsKRTest (f : Y → ℝ) : Prop where
  measurable : Measurable f
  lipschitz : LipschitzWith 1 f
  bounded : ∃ C, ∀ y, |f y| ≤ C

/-- `W₁(μ, ν) ≤ c` in Kantorovich–Rubinstein DUAL form, tested on bounded
measurable 1-Lipschitz functions. -/
def W1DualLE (μ ν : Measure Y) (c : ℝ) : Prop :=
  ∀ f : Y → ℝ, IsKRTest f → |∫ y, f y ∂μ - ∫ y, f y ∂ν| ≤ c

namespace IsKRTest

theorem integrable {f : Y → ℝ} (hf : IsKRTest f) (μ : Measure Y) [IsFiniteMeasure μ] :
    Integrable f μ := by
  obtain ⟨C, hC⟩ := hf.bounded
  exact Integrable.of_bound hf.measurable.aestronglyMeasurable C
    (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)

theorem zero : IsKRTest (fun _ : Y => (0 : ℝ)) :=
  ⟨measurable_const, LipschitzWith.of_dist_le_mul fun _ _ => by simp, ⟨0, fun _ => by simp⟩⟩

theorem neg {f : Y → ℝ} (hf : IsKRTest f) : IsKRTest (fun y => -f y) := by
  refine ⟨hf.measurable.neg, ?_, ?_⟩
  · exact LipschitzWith.of_dist_le_mul fun a b => by
      simpa [Real.dist_eq, abs_sub_comm, neg_sub_neg] using hf.lipschitz.dist_le_mul a b
  · obtain ⟨C, hC⟩ := hf.bounded
    exact ⟨C, fun y => by simpa using hC y⟩

end IsKRTest

namespace W1DualLE

variable {μ ν ρ : Measure Y} {c d : ℝ}

theorem mono (h : W1DualLE μ ν c) (hcd : c ≤ d) : W1DualLE μ ν d :=
  fun f hf => (h f hf).trans hcd

theorem nonneg (h : W1DualLE μ ν c) : 0 ≤ c := by
  have := h _ IsKRTest.zero
  simpa using this

theorem symm (h : W1DualLE μ ν c) : W1DualLE ν μ c :=
  fun f hf => by rw [abs_sub_comm]; exact h f hf

theorem refl (μ : Measure Y) : W1DualLE μ μ 0 := fun f _ => by simp

/-- Triangle inequality. -/
theorem trans (h₁ : W1DualLE μ ν c) (h₂ : W1DualLE ν ρ d) : W1DualLE μ ρ (c + d) :=
  fun f hf => (abs_sub_le _ _ _).trans (add_le_add (h₁ f hf) (h₂ f hf))

/-- Closedness: a bound holding along a sequence `cₙ → L` holds at `L`. -/
theorem of_tendsto {c : ℕ → ℝ} {L : ℝ} (h : ∀ n, W1DualLE μ ν (c n))
    (hc : Tendsto c atTop (𝓝 L)) : W1DualLE μ ν L :=
  fun f hf => ge_of_tendsto' hc fun n => h n f hf

end W1DualLE

/-- **Mixture of pointwise defects.** If `W₁(κ y, η y) ≤ δ` for EVERY `y`, then
`W₁(κ ∘ μ, η ∘ μ) ≤ δ` for every probability law `μ`. -/
theorem W1DualLE.comp_of_forall (μ : Measure Y) [IsProbabilityMeasure μ]
    (κ η : Kernel Y Y) [IsMarkovKernel κ] [IsMarkovKernel η] {δ : ℝ}
    (h : ∀ y, W1DualLE (κ y) (η y) δ) : W1DualLE (κ ∘ₘ μ) (η ∘ₘ μ) δ := by
  intro f hf
  obtain ⟨C, hC⟩ := hf.bounded
  have hint : ∀ (θ : Kernel Y Y) [IsMarkovKernel θ],
      ∫ y, f y ∂(θ ∘ₘ μ) = ∫ x, ∫ y, f y ∂θ x ∂μ := by
    intro θ _
    rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp]
    · rfl
    · rw [← Measure.comp_eq_comp_const_apply]; exact hf.integrable _
  have hmeas : ∀ (θ : Kernel Y Y) [IsMarkovKernel θ],
      StronglyMeasurable fun x => ∫ y, f y ∂θ x :=
    fun θ _ => hf.measurable.stronglyMeasurable.integral_kernel
  have hbd : ∀ (θ : Kernel Y Y) [IsMarkovKernel θ] (x : Y), ‖∫ y, f y ∂θ x‖ ≤ C := by
    intro θ _ x
    have := norm_integral_le_of_norm_le_const (μ := θ x) (C := C) (f := f)
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hC y)
    simpa using this
  have hI : ∀ (θ : Kernel Y Y) [IsMarkovKernel θ], Integrable (fun x => ∫ y, f y ∂θ x) μ :=
    fun θ _ => Integrable.of_bound (hmeas θ).aestronglyMeasurable C
      (Eventually.of_forall (hbd θ))
  rw [hint κ, hint η, ← integral_sub (hI κ) (hI η)]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := δ)
    (f := fun x => ∫ y, f y ∂κ x - ∫ y, f y ∂η x)
    (Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using h x f hf)
  simpa [Real.norm_eq_abs] using this

/-- **Pushforward by an `L`-Lipschitz measurable map** scales the bound by `L`. -/
theorem W1DualLE.map_lipschitz {V : Type uV} [PseudoMetricSpace V] [MeasurableSpace V]
    {μ ν : Measure Y} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {c : ℝ}
    (hc : W1DualLE μ ν c) {h : Y → V} (hh : Measurable h) {L : ℝ≥0}
    (hL : LipschitzWith L h) : W1DualLE (μ.map h) (ν.map h) (L * c) := by
  intro f hf
  rw [integral_map hh.aemeasurable hf.measurable.aestronglyMeasurable,
    integral_map hh.aemeasurable hf.measurable.aestronglyMeasurable]
  have hne : Nonempty Y := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := measure_univ (μ := μ)
    simp [Set.univ_eq_empty_iff.mpr hne] at this
  obtain ⟨y₀⟩ := hne
  rcases eq_or_ne L 0 with hL0 | hLne0
  · -- `f ∘ h` is constant
    subst hL0
    have hconst : ∀ y, f (h y) = f (h y₀) := by
      intro y
      have h1 := hf.lipschitz.dist_le_mul (h y) (h y₀)
      have h2 := hL.dist_le_mul y y₀
      simp only [NNReal.coe_zero, zero_mul, NNReal.coe_one, one_mul] at h1 h2
      exact dist_le_zero.mp (h1.trans h2)
    simp only [hconst, integral_const, probReal_univ, one_smul, sub_self, abs_zero,
      NNReal.coe_zero, zero_mul, le_refl]
  · have hLpos' : (0 : ℝ) < L := by
      exact_mod_cast pos_iff_ne_zero.mpr hLne0
    have hLne : (L : ℝ) ≠ 0 := hLpos'.ne'
    let g : Y → ℝ := fun y => (L : ℝ)⁻¹ * f (h y)
    have hg : IsKRTest g := by
      refine ⟨measurable_const.mul (hf.measurable.comp hh), ?_, ?_⟩
      · refine LipschitzWith.of_dist_le_mul fun a b => ?_
        have h1 := hf.lipschitz.dist_le_mul (h a) (h b)
        have h2 := hL.dist_le_mul a b
        simp only [NNReal.coe_one, one_mul] at h1
        change dist ((L : ℝ)⁻¹ * f (h a)) ((L : ℝ)⁻¹ * f (h b)) ≤ _
        rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hLpos'),
          ← Real.dist_eq]
        calc (L : ℝ)⁻¹ * dist (f (h a)) (f (h b))
            ≤ (L : ℝ)⁻¹ * (L * dist a b) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) (inv_nonneg.mpr hLpos'.le)
          _ = ((1 : ℝ≥0) : ℝ) * dist a b := by
              rw [inv_mul_cancel_left₀ hLne]; simp
      · obtain ⟨C, hC⟩ := hf.bounded
        refine ⟨(L : ℝ)⁻¹ * C, fun y => ?_⟩
        change |(L : ℝ)⁻¹ * f (h y)| ≤ _
        rw [abs_mul, abs_of_pos (inv_pos.mpr hLpos')]
        exact mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr hLpos'.le)
    have := hc g hg
    simp only [g, integral_const_mul, ← mul_sub, abs_mul,
      abs_of_pos (inv_pos.mpr hLpos')] at this
    rwa [inv_mul_le_iff₀ hLpos'] at this

/-- Finite first moments give a finite dual bound. -/
theorem W1DualLE.of_integrable_dist (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (y₀ : Y) (hμ : Integrable (fun y => dist y y₀) μ)
    (hν : Integrable (fun y => dist y y₀) ν) :
    W1DualLE μ ν (∫ y, dist y y₀ ∂μ + ∫ y, dist y y₀ ∂ν) := by
  intro f hf
  have key : ∀ (θ : Measure Y) [IsProbabilityMeasure θ],
      Integrable (fun y => dist y y₀) θ → |∫ y, f y ∂θ - f y₀| ≤ ∫ y, dist y y₀ ∂θ := by
    intro θ _ hθ
    have hsub : ∫ y, f y ∂θ - f y₀ = ∫ y, (f y - f y₀) ∂θ := by
      rw [integral_sub (hf.integrable θ) (integrable_const _), integral_const,
        probReal_univ, one_smul]
    rw [hsub]
    refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
      (Eventually.of_forall fun _ => abs_nonneg _) hθ (Eventually.of_forall fun y => ?_))
    have := hf.lipschitz.dist_le_mul y y₀
    simpa [Real.dist_eq] using this
  have h1 := key μ hμ
  have h2 := key ν hν
  calc |∫ y, f y ∂μ - ∫ y, f y ∂ν|
      = |(∫ y, f y ∂μ - f y₀) - (∫ y, f y ∂ν - f y₀)| := by ring_nf
    _ ≤ |∫ y, f y ∂μ - f y₀| + |∫ y, f y ∂ν - f y₀| := abs_sub _ _
    _ ≤ _ := add_le_add h1 h2

end PermanssonResearch.Probability
