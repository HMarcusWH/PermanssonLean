import PermanssonLean.Probability.TotalVariation
import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Tactic

/-!
# Event total-variation calculus (general measurable spaces)

The frozen core freezes the paper's convention
`‖μ − ν‖_TV = sup_A |μ(A) − ν(A)|` (`PermanssonLean.ProbabilitySupport.eventTotalVariation`).
Proposition 5.4 and A2 bound it through common-part kernels, which need
`MeasurableSpace.CountableOrCountablyGenerated` instances. The lemmas here need
NO countability or standard-Borel hypothesis:

* `lintegral_le_add_eventTotalVariation`: for measurable `f` with `0 ≤ f ≤ 1`,
  `∫ f dμ ≤ ∫ f dν + TV(μ,ν)` (via a Hahn decomposition of `(ν, μ)`);
* `eventTotalVariation_map_le`: pushforwards contract event TV;
* `eventTotalVariation_triangle`;
* `eventTotalVariation_compProd_right_le`: same first law, kernels within `η`
  pointwise ⇒ compositions within `η`;
* `eventTotalVariation_compProd_left_le`: same kernel ⇒ compositions within
  the TV of the first laws.

These are the analytic ingredients of the E1 linear approximate-quotient bound.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Probability

set_option autoImplicit false

open PermanssonLean.ProbabilitySupport

universe uΩ uZ uW
variable {Ω : Type uΩ} {Z : Type uZ} {W : Type uW}
variable [MeasurableSpace Ω] [MeasurableSpace Z] [MeasurableSpace W]

/-- Finite ENNReal values within an additive `ofReal η` of each other in both
directions are within `η` as reals. -/
theorem abs_toReal_sub_le_of_le_add
    {a b : ℝ≥0∞} (ha : a ≠ ∞) (hb : b ≠ ∞) {η : ℝ} (hη : 0 ≤ η)
    (hab : a ≤ b + ENNReal.ofReal η) (hba : b ≤ a + ENNReal.ofReal η) :
    |a.toReal - b.toReal| ≤ η := by
  have h1 : a.toReal ≤ b.toReal + η := by
    have := ENNReal.toReal_mono (by simp [hb]) hab
    rwa [ENNReal.toReal_add hb ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hη] at this
  have h2 : b.toReal ≤ a.toReal + η := by
    have := ENNReal.toReal_mono (by simp [ha]) hba
    rwa [ENNReal.toReal_add ha ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hη] at this
  rw [abs_le]
  constructor <;> linarith

/-- A measurable event discrepancy, in ENNReal form, is within event TV. -/
theorem measure_le_add_eventTotalVariation
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {s : Set Ω} (hs : MeasurableSet s) :
    μ s ≤ ν s + ENNReal.ofReal (eventTotalVariation μ ν) := by
  have habs := abs_measureReal_sub_le_eventTotalVariation μ ν hs
  have hle : μ.real s ≤ ν.real s + eventTotalVariation μ ν := by
    have := le_abs_self (μ.real s - ν.real s)
    linarith
  calc
    μ s = ENNReal.ofReal (μ.real s) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal (ν.real s + eventTotalVariation μ ν) :=
      ENNReal.ofReal_le_ofReal hle
    _ = ENNReal.ofReal (ν.real s) + ENNReal.ofReal (eventTotalVariation μ ν) :=
      ENNReal.ofReal_add measureReal_nonneg (eventTotalVariation_nonneg μ ν)
    _ = ν s + ENNReal.ofReal (eventTotalVariation μ ν) := by
      rw [ofReal_measureReal (measure_ne_top _ _)]

/-- **Integral-within-TV.** For measurable `0 ≤ f ≤ 1`,
`∫ f dμ ≤ ∫ f dν + TV(μ,ν)`. Proof by a Hahn decomposition of `(ν, μ)`;
no countability hypothesis on `Ω`. -/
theorem lintegral_le_add_eventTotalVariation
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ ω, f ω ≤ 1) :
    ∫⁻ ω, f ω ∂μ ≤ ∫⁻ ω, f ω ∂ν + ENNReal.ofReal (eventTotalVariation μ ν) := by
  obtain ⟨t, ht⟩ := exists_isHahnDecomposition ν μ
  have htm : MeasurableSet t := ht.measurableSet
  -- on t: ν ≤ μ ; on tᶜ: μ ≤ ν
  have hle_t : ν.restrict t ≤ μ.restrict t := ht.le_on
  have hle_c : μ.restrict tᶜ ≤ ν.restrict tᶜ := ht.ge_on_compl
  have hcompl : ∫⁻ ω in tᶜ, f ω ∂μ ≤ ∫⁻ ω in tᶜ, f ω ∂ν :=
    lintegral_mono' hle_c le_rfl
  have hdecomp : μ.restrict t = (μ.restrict t - ν.restrict t) + ν.restrict t :=
    (Measure.sub_add_cancel_of_le hle_t).symm
  have hexcess : ∫⁻ ω, f ω ∂(μ.restrict t - ν.restrict t) ≤ μ t - ν t := by
    calc
      ∫⁻ ω, f ω ∂(μ.restrict t - ν.restrict t) ≤
          ∫⁻ _ω, 1 ∂(μ.restrict t - ν.restrict t) := lintegral_mono hf1
      _ = (μ.restrict t - ν.restrict t) Set.univ := by rw [lintegral_one]
      _ = μ.restrict t Set.univ - ν.restrict t Set.univ :=
        Measure.sub_apply MeasurableSet.univ hle_t
      _ = μ t - ν t := by
        rw [Measure.restrict_apply MeasurableSet.univ,
          Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
  have hgap : μ t - ν t ≤ ENNReal.ofReal (eventTotalVariation μ ν) :=
    tsub_le_iff_left.mpr (measure_le_add_eventTotalVariation μ ν htm)
  have hon_t : ∫⁻ ω in t, f ω ∂μ ≤
      ∫⁻ ω in t, f ω ∂ν + ENNReal.ofReal (eventTotalVariation μ ν) := by
    calc
      ∫⁻ ω in t, f ω ∂μ =
          ∫⁻ ω, f ω ∂(μ.restrict t - ν.restrict t) + ∫⁻ ω in t, f ω ∂ν := by
        conv_lhs => rw [hdecomp]
        rw [lintegral_add_measure]
      _ ≤ ENNReal.ofReal (eventTotalVariation μ ν) + ∫⁻ ω in t, f ω ∂ν :=
        add_le_add (hexcess.trans hgap) le_rfl
      _ = _ := add_comm _ _
  calc
    ∫⁻ ω, f ω ∂μ = ∫⁻ ω in t, f ω ∂μ + ∫⁻ ω in tᶜ, f ω ∂μ :=
      (lintegral_add_compl f htm).symm
    _ ≤ (∫⁻ ω in t, f ω ∂ν + ENNReal.ofReal (eventTotalVariation μ ν)) +
          ∫⁻ ω in tᶜ, f ω ∂ν := add_le_add hon_t hcompl
    _ = (∫⁻ ω in t, f ω ∂ν + ∫⁻ ω in tᶜ, f ω ∂ν) +
          ENNReal.ofReal (eventTotalVariation μ ν) := by ring
    _ = ∫⁻ ω, f ω ∂ν + ENNReal.ofReal (eventTotalVariation μ ν) := by
      rw [lintegral_add_compl f htm]

/-- Real two-sided form of the integral-within-TV bound. -/
theorem abs_lintegral_toReal_sub_le_eventTotalVariation
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → ℝ≥0∞} (hf : Measurable f) (hf1 : ∀ ω, f ω ≤ 1) :
    |(∫⁻ ω, f ω ∂μ).toReal - (∫⁻ ω, f ω ∂ν).toReal| ≤
      eventTotalVariation μ ν := by
  have hfin : ∀ ρ : Measure Ω, IsProbabilityMeasure ρ → ∫⁻ ω, f ω ∂ρ ≠ ∞ :=
    fun ρ _ => ne_top_of_le_ne_top (measure_ne_top ρ Set.univ)
      ((lintegral_mono hf1).trans_eq (lintegral_one))
  refine abs_toReal_sub_le_of_le_add (hfin μ inferInstance) (hfin ν inferInstance)
    (eventTotalVariation_nonneg μ ν)
    (lintegral_le_add_eventTotalVariation μ ν hf hf1) ?_
  rw [eventTotalVariation_symm]
  exact lintegral_le_add_eventTotalVariation ν μ hf hf1

/-- Two probability measures whose measurable events agree up to an additive
`η` in both directions are within `η` in event TV. -/
theorem eventTotalVariation_le_of_forall
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ s, MeasurableSet s →
      μ s ≤ ν s + ENNReal.ofReal η ∧ ν s ≤ μ s + ENNReal.ofReal η) :
    eventTotalVariation μ ν ≤ η := by
  unfold eventTotalVariation
  apply csSup_le (eventTVCandidates_nonempty μ ν)
  rintro r ⟨s, hs, rfl⟩
  exact abs_toReal_sub_le_of_le_add (measure_ne_top _ _) (measure_ne_top _ _)
    hη (h s hs).1 (h s hs).2

/-- Pushforwards contract event total variation. -/
theorem eventTotalVariation_map_le
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : Ω → Z} (hf : Measurable f) :
    eventTotalVariation (μ.map f) (ν.map f) ≤ eventTotalVariation μ ν := by
  unfold eventTotalVariation
  apply csSup_le (eventTVCandidates_nonempty _ _)
  rintro r ⟨s, hs, rfl⟩
  rw [map_measureReal_apply hf hs, map_measureReal_apply hf hs]
  exact abs_measureReal_sub_le_eventTotalVariation μ ν (hf hs)

/-- Triangle inequality for event total variation. -/
theorem eventTotalVariation_triangle
    (μ ν ρ : Measure Ω)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    eventTotalVariation μ ρ ≤ eventTotalVariation μ ν + eventTotalVariation ν ρ := by
  unfold eventTotalVariation
  apply csSup_le (eventTVCandidates_nonempty μ ρ)
  rintro r ⟨s, hs, rfl⟩
  have h1 := abs_measureReal_sub_le_eventTotalVariation μ ν hs
  have h2 := abs_measureReal_sub_le_eventTotalVariation ν ρ hs
  calc
    |μ.real s - ρ.real s| ≤ |μ.real s - ν.real s| + |ν.real s - ρ.real s| :=
      abs_sub_le _ _ _
    _ ≤ _ := add_le_add h1 h2

/-- **Same first law, kernels within `η`.** -/
theorem eventTotalVariation_compProd_right_le
    (α : Measure Ω) [IsProbabilityMeasure α]
    (κ ι : Kernel Ω Z) [IsMarkovKernel κ] [IsMarkovKernel ι]
    {η : ℝ} (hη : 0 ≤ η)
    (h : ∀ ω, eventTotalVariation (κ ω) (ι ω) ≤ η) :
    eventTotalVariation (α ⊗ₘ κ) (α ⊗ₘ ι) ≤ η := by
  refine eventTotalVariation_le_of_forall _ _ hη fun C hC => ?_
  have hpt : ∀ (κ₁ κ₂ : Kernel Ω Z) [IsMarkovKernel κ₁] [IsMarkovKernel κ₂],
      (∀ ω, eventTotalVariation (κ₁ ω) (κ₂ ω) ≤ η) →
      (α ⊗ₘ κ₁) C ≤ (α ⊗ₘ κ₂) C + ENNReal.ofReal η := by
    intro κ₁ κ₂ _ _ hk
    rw [Measure.compProd_apply hC, Measure.compProd_apply hC]
    calc
      ∫⁻ ω, κ₁ ω (Prod.mk ω ⁻¹' C) ∂α ≤
          ∫⁻ ω, (κ₂ ω (Prod.mk ω ⁻¹' C) + ENNReal.ofReal η) ∂α := by
        refine lintegral_mono fun ω => ?_
        exact (measure_le_add_eventTotalVariation (κ₁ ω) (κ₂ ω)
          (measurable_prodMk_left hC)).trans
          (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hk ω)))
      _ = ∫⁻ ω, κ₂ ω (Prod.mk ω ⁻¹' C) ∂α + ENNReal.ofReal η := by
        rw [lintegral_add_right _ measurable_const, lintegral_const,
          measure_univ, mul_one]
  exact ⟨hpt κ ι h, hpt ι κ fun ω => (eventTotalVariation_symm _ _).le.trans (h ω)⟩

/-- **Same kernel, different first laws.** -/
theorem eventTotalVariation_compProd_left_le
    (α β : Measure Ω) [IsProbabilityMeasure α] [IsProbabilityMeasure β]
    (κ : Kernel Ω Z) [IsMarkovKernel κ] :
    eventTotalVariation (α ⊗ₘ κ) (β ⊗ₘ κ) ≤ eventTotalVariation α β := by
  refine eventTotalVariation_le_of_forall _ _ (eventTotalVariation_nonneg α β)
    fun C hC => ?_
  have hmeas : Measurable (fun ω => κ ω (Prod.mk ω ⁻¹' C)) :=
    Kernel.measurable_kernel_prodMk_left hC
  have hle1 : ∀ ω, κ ω (Prod.mk ω ⁻¹' C) ≤ 1 := fun ω => prob_le_one
  rw [Measure.compProd_apply hC, Measure.compProd_apply hC]
  refine ⟨lintegral_le_add_eventTotalVariation α β hmeas hle1, ?_⟩
  rw [eventTotalVariation_symm]
  exact lintegral_le_add_eventTotalVariation β α hmeas hle1

end PermanssonResearch.Probability
