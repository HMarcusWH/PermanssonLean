import PermanssonResearch.Probability.EventTVCalculus

/-! Q-LOCAL: errors are averaged under the first process's actual history law.
The history type may store complete chronological histories. Each evolution
uses its own declared kernel; an initial-law mismatch is retained explicitly. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.Probability

open PermanssonLean.ProbabilitySupport

variable {H Z : Type*} [MeasurableSpace H] [MeasurableSpace Z]

theorem eventTV_compProd_averaged
    (μ : Measure H) [IsProbabilityMeasure μ]
    (K L : Kernel H Z) [IsMarkovKernel K] [IsMarkovKernel L]
    (d : H → ℝ) (hd : Measurable d) (hd0 : ∀ h, 0 ≤ d h)
    {e : ℝ} (he : 0 ≤ e)
    (hrows : ∀ h, eventTotalVariation (K h) (L h) ≤ d h)
    (haverage : ∫⁻ h, ENNReal.ofReal (d h) ∂μ ≤ ENNReal.ofReal e) :
    eventTotalVariation (μ ⊗ₘ K) (μ ⊗ₘ L) ≤ e := by
  refine eventTotalVariation_le_of_forall _ _ he fun C hC => ?_
  have hdm : Measurable (fun h => ENNReal.ofReal (d h)) := hd.ennreal_ofReal
  have hone : ∀ (K₁ K₂ : Kernel H Z) [IsMarkovKernel K₁] [IsMarkovKernel K₂],
      (∀ h, eventTotalVariation (K₁ h) (K₂ h) ≤ d h) →
      (μ ⊗ₘ K₁) C ≤ (μ ⊗ₘ K₂) C + ENNReal.ofReal e := by
    intro K₁ K₂ _ _ hk
    rw [Measure.compProd_apply hC, Measure.compProd_apply hC]
    calc
      ∫⁻ h, K₁ h (Prod.mk h ⁻¹' C) ∂μ ≤
          ∫⁻ h, (K₂ h (Prod.mk h ⁻¹' C) + ENNReal.ofReal (d h)) ∂μ := by
        apply lintegral_mono
        intro h
        exact (measure_le_add_eventTotalVariation (K₁ h) (K₂ h)
          (measurable_prodMk_left hC)).trans
          (add_le_add le_rfl (ENNReal.ofReal_le_ofReal (hk h)))
      _ = (∫⁻ h, K₂ h (Prod.mk h ⁻¹' C) ∂μ) +
          ∫⁻ h, ENNReal.ofReal (d h) ∂μ := lintegral_add_right _ hdm
      _ ≤ _ := add_le_add le_rfl haverage
  exact ⟨hone K L hrows,
    hone L K (fun h => (eventTotalVariation_symm _ _).le.trans (hrows h))⟩

noncomputable def historyEvolution (μ : Measure H) (K : ℕ → Kernel H Z)
    (append : ℕ → H × Z → H) : ℕ → Measure H
  | 0 => μ
  | n + 1 => (historyEvolution μ K append n ⊗ₘ K n).map (append n)

theorem historyEvolution_isProbability (μ : Measure H) [IsProbabilityMeasure μ]
    (K : ℕ → Kernel H Z) [∀ n, IsMarkovKernel (K n)]
    (append : ℕ → H × Z → H) (hm : ∀ n, Measurable (append n)) (n : ℕ) :
    IsProbabilityMeasure (historyEvolution μ K append n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih =>
    letI := ih
    exact (Measure.isProbabilityMeasure_map_iff (hm n).aemeasurable).mpr inferInstance

theorem historyEvolution_tv_le_sum
    (μ ν : Measure H) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K L : ℕ → Kernel H Z) [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (L n)]
    (append : ℕ → H × Z → H) (hm : ∀ n, Measurable (append n))
    (d : ℕ → H → ℝ) (hd : ∀ n, Measurable (d n)) (hd0 : ∀ n h, 0 ≤ d n h)
    (e : ℕ → ℝ) (he : ∀ n, 0 ≤ e n)
    (hrows : ∀ n h, eventTotalVariation (K n h) (L n h) ≤ d n h)
    (haverage : ∀ n, ∫⁻ h, ENNReal.ofReal (d n h)
      ∂historyEvolution μ K append n ≤ ENNReal.ofReal (e n))
    {ε : ℝ} (hε : eventTotalVariation μ ν ≤ ε) (T : ℕ) :
    eventTotalVariation (historyEvolution μ K append T) (historyEvolution ν L append T) ≤
      min 1 (ε + ∑ t ∈ Finset.range T, e t) := by
  have hprobK (n) := historyEvolution_isProbability μ K append hm n
  have hprobL (n) := historyEvolution_isProbability ν L append hm n
  have hsum : ∀ n, eventTotalVariation
      (historyEvolution μ K append n) (historyEvolution ν L append n) ≤
        ε + ∑ t ∈ Finset.range n, e t := by
    intro n
    induction n with
    | zero => simpa [historyEvolution] using hε
    | succ n ih =>
      letI := hprobK n
      letI := hprobL n
      have hr := eventTV_compProd_averaged (historyEvolution μ K append n)
        (K n) (L n) (d n) (hd n) (hd0 n) (he n) (hrows n) (haverage n)
      have hl := eventTotalVariation_compProd_left_le
        (historyEvolution μ K append n) (historyEvolution ν L append n) (L n)
      have ht := eventTotalVariation_triangle
        (historyEvolution μ K append n ⊗ₘ K n)
        (historyEvolution μ K append n ⊗ₘ L n)
        (historyEvolution ν L append n ⊗ₘ L n)
      have hp := eventTotalVariation_map_le
        (historyEvolution μ K append n ⊗ₘ K n)
        (historyEvolution ν L append n ⊗ₘ L n) (hm n)
      change eventTotalVariation
        ((historyEvolution μ K append n ⊗ₘ K n).map (append n))
        ((historyEvolution ν L append n ⊗ₘ L n).map (append n)) ≤ _
      rw [Finset.sum_range_succ]
      linarith
  letI := hprobK T
  letI := hprobL T
  exact le_min (eventTotalVariation_le_one _ _) (hsum T)

end PermanssonResearch.Probability
