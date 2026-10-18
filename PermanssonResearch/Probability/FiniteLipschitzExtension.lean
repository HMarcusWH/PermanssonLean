import PermanssonResearch.Probability.FiniteKantorovichDuality

/-! Bounded McShane extensions of finite metric tests. Clipping keeps the
original bounded test class while fixing every specified center value. -/

open MeasureTheory
open scoped BigOperators
namespace PermanssonResearch.Probability.FiniteLipschitzExtension
set_option autoImplicit false

variable {I Y : Type*} [Fintype I] [Nonempty I] [PseudoMetricSpace Y]

noncomputable def raw (c : I → Y) (f : I → ℝ) (y : Y) : ℝ := ⨅ i, dist y (c i)+f i

theorem raw_le (c : I → Y) (f : I → ℝ) (y : Y) (i : I) :
    raw c f y ≤ dist y (c i)+f i := ciInf_le (Set.finite_range _).bddBelow i

theorem raw_lipschitz (c : I → Y) (f : I → ℝ) : LipschitzWith 1 (raw c f) := by
  apply LipschitzWith.of_le_add
  intro x y
  have h : raw c f x-dist x y ≤ raw c f y := by
    apply le_ciInf
    intro i
    have hx := raw_le c f x i
    have ht := dist_triangle x y (c i)
    linarith
  linarith

theorem raw_center (c : I → Y) (f : I → ℝ)
    (hf : ∀ i j, |f i-f j| ≤ dist (c i) (c j)) (i : I) : raw c f (c i) = f i := by
  apply le_antisymm
  · simpa using raw_le c f (c i) i
  · apply le_ciInf
    intro j
    have h := (le_abs_self _).trans (hf i j)
    linarith

noncomputable def radius (f : I → ℝ) : ℝ := ∑ i, |f i|

theorem radius_nonneg (f : I → ℝ) : 0 ≤ radius f :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem value_le_radius (f : I → ℝ) (i : I) : |f i| ≤ radius f := by
  change |f i| ≤ ∑ j, |f j|
  exact Finset.single_le_sum (fun j _ => abs_nonneg (f j)) (Finset.mem_univ i)

noncomputable def extension (c : I → Y) (f : I → ℝ) (y : Y) : ℝ :=
  max (min (raw c f y) (radius f)) (-radius f)

theorem extension_lipschitz (c : I → Y) (f : I → ℝ) :
    LipschitzWith 1 (extension c f) := ((raw_lipschitz c f).min_const _).max_const _

theorem extension_bounded (c : I → Y) (f : I → ℝ) (y : Y) :
    |extension c f y| ≤ radius f := by
  apply abs_le.mpr
  exact ⟨le_max_right _ _,max_le (min_le_right _ _) (by linarith [radius_nonneg f])⟩

theorem extension_center (c : I → Y) (f : I → ℝ)
    (hf : ∀ i j, |f i-f j| ≤ dist (c i) (c j)) (i : I) : extension c f (c i) = f i := by
  dsimp [extension]
  rw [raw_center c f hf,min_eq_left (abs_le.mp (value_le_radius f i)).2,
    max_eq_left (abs_le.mp (value_le_radius f i)).1]

theorem extension_error (c : I → Y) (f : I → ℝ)
    (hf : ∀ i j, |f i-f j| ≤ dist (c i) (c j)) (t : Y → I) (y : Y) :
    |extension c f y-f (t y)| ≤ dist y (c (t y)) := by
  have h := (extension_lipschitz c f).dist_le_mul y (c (t y))
  simpa [Real.dist_eq,extension_center c f hf] using h

variable [MeasurableSpace Y] [BorelSpace Y]

theorem extension_isKRTest (c : I → Y) (f : I → ℝ) : IsKRTest (extension c f) :=
  ⟨(extension_lipschitz c f).continuous.measurable,extension_lipschitz c f,
    ⟨radius f,extension_bounded c f⟩⟩

variable [MeasurableSpace I] [MeasurableSingletonClass I]

theorem integral_extension_error (μ : Measure Y) [IsProbabilityMeasure μ]
    (c : I → Y) (f : I → ℝ) (hf : ∀ i j, |f i-f j| ≤ dist (c i) (c j))
    (t : Y → I) (ht : Measurable t)
    (he : Integrable (fun y => dist y (c (t y))) μ) :
    |(∫ y, f (t y) ∂μ)-(∫ y, extension c f y ∂μ)| ≤
      ∫ y, dist y (c (t y)) ∂μ := by
  have hfint : Integrable (fun y => f (t y)) μ :=
    Integrable.of_bound ((measurable_of_finite f).comp ht).aestronglyMeasurable (radius f)
      (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using value_le_radius f (t y))
  have hgint := (extension_isKRTest c f).integrable μ
  rw [← integral_sub hfint hgint]
  apply abs_integral_le_integral_abs.trans
  apply integral_mono (hfint.sub hgint).abs he
  intro y
  simpa [abs_sub_comm] using extension_error c f hf t y

/-- A quantized pair inherits the original dual bound plus the two actual
quantization errors, on the induced finite pseudometric without injectivity. -/
theorem finite_pushforward_dual_bound (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (c : I → Y) (t : Y → I) (ht : Measurable t)
    (hμ : Integrable (fun y => dist y (c (t y))) μ)
    (hν : Integrable (fun y => dist y (c (t y))) ν) {b : ℝ} (hb : W1DualLE μ ν b) :
    letI : PseudoMetricSpace I := PseudoMetricSpace.induced c inferInstance
    W1DualLE (μ.map t) (ν.map t)
      (b+(∫ y, dist y (c (t y)) ∂μ)+(∫ y, dist y (c (t y)) ∂ν)) := by
  letI : PseudoMetricSpace I := PseudoMetricSpace.induced c inferInstance
  intro f hf
  have hp : ∀ i j, |f i-f j| ≤ dist (c i) (c j) := by
    intro i j
    have h := hf.lipschitz.dist_le_mul i j
    change dist (f i) (f j) ≤ (1 : ℝ) * dist (c i) (c j) at h
    simpa [Real.dist_eq] using h
  rw [integral_map ht.aemeasurable hf.measurable.aestronglyMeasurable,
    integral_map ht.aemeasurable hf.measurable.aestronglyMeasurable]
  have heμ := integral_extension_error μ c f hp t ht hμ
  have heν := integral_extension_error ν c f hp t ht hν
  have hg := hb (extension c f) (extension_isKRTest c f)
  have h₁ := abs_sub_le (∫ y, f (t y) ∂μ) (∫ y, extension c f y ∂μ)
    (∫ y, f (t y) ∂ν)
  have h₂ := abs_sub_le (∫ y, extension c f y ∂μ) (∫ y, extension c f y ∂ν)
    (∫ y, f (t y) ∂ν)
  rw [abs_sub_comm (∫ y, extension c f y ∂ν) (∫ y, f (t y) ∂ν)] at h₂
  linarith

end PermanssonResearch.Probability.FiniteLipschitzExtension
