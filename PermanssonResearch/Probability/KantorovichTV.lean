import PermanssonResearch.Probability.KantorovichDual
import PermanssonResearch.Probability.EventTVCalculus

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory


/-!
# A3.4 — Total variation versus dual `W₁`

* Proved conversion with an explicit diameter factor: if every distance is at
  most `D`, then `W₁ ≤ D · TV` (`W1DualLE.of_eventTV`, via the E1 Hahn-decomposition
  bound for `[0,1]`-valued functions).
* Firewall for unbounded metrics: on `ℝ`, for every `ε ∈ (0,1]` and every constant
  `C`, some pair has event TV at most `ε` but dual `W₁` above `C ε`
  (`tv_does_not_control_w1_on_real`). A TV primitive budget may therefore not be
  substituted into (V20.18) without a proved conversion.
-/

namespace PermanssonResearch.Probability

set_option autoImplicit false

open PermanssonLean.ProbabilitySupport

universe uY
variable {Y : Type uY} [PseudoMetricSpace Y] [MeasurableSpace Y]

/-- **A3.4 (proved conversion, bounded metric).** If every distance is at most
`D`, then `W₁ ≤ D · TV` (event total variation). No such conversion is claimed for
unbounded metrics (`tv_does_not_control_w1_on_real`). -/
theorem W1DualLE.of_eventTV (μ ν : Measure Y) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {D : ℝ} (hD0 : 0 ≤ D) (hD : ∀ a b : Y, dist a b ≤ D) :
    W1DualLE μ ν (D * eventTotalVariation μ ν) := by
  intro f hf
  have hne : Nonempty Y := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have := measure_univ (μ := μ)
    simp [Set.univ_eq_empty_iff.mpr hne] at this
  obtain ⟨C, hC⟩ := hf.bounded
  have hbdd : BddBelow (Set.range f) :=
    ⟨-C, by rintro _ ⟨y, rfl⟩; exact neg_le_of_abs_le (hC y)⟩
  set m := ⨅ y, f y with hm
  have hg0 : ∀ y, 0 ≤ f y - m := fun y => sub_nonneg.mpr (ciInf_le hbdd y)
  have hgD : ∀ y, f y - m ≤ D := by
    intro y
    have : f y - D ≤ m := le_ciInf fun y' => by
      have := hf.lipschitz.dist_le_mul y y'
      simp only [NNReal.coe_one, one_mul] at this
      have h2 : f y - f y' ≤ dist y y' :=
        (le_abs_self (f y - f y')).trans (by simpa [Real.dist_eq] using this)
      linarith [hD y y']
    linarith
  have hshift : ∀ (θ : Measure Y) [IsProbabilityMeasure θ],
      ∫ y, f y ∂θ = ∫ y, (f y - m) ∂θ + m := by
    intro θ _
    rw [integral_sub (hf.integrable θ) (integrable_const _), integral_const, probReal_univ,
      one_smul]; ring
  rw [hshift μ, hshift ν, add_sub_add_right_eq_sub]
  have hTV0 : 0 ≤ eventTotalVariation μ ν := (abs_nonneg _).trans
    (abs_measureReal_sub_le_eventTotalVariation μ ν MeasurableSet.univ)
  rcases hD0.eq_or_lt with hD0' | hDpos
  · have hz : ∀ y, f y - m = 0 := fun y => le_antisymm (by linarith [hgD y, hD0'.symm]) (hg0 y)
    simp [hz, ← hD0']
  · -- normalise to `[0,1]` and use the E1 Hahn-decomposition bound
    let k : Y → ℝ≥0∞ := fun y => ENNReal.ofReal ((f y - m) / D)
    have hkm : Measurable k := ENNReal.measurable_ofReal.comp
      ((hf.measurable.sub measurable_const).div_const D)
    have hk1 : ∀ y, k y ≤ 1 := fun y => by
      simp only [k]
      rw [ENNReal.ofReal_le_one]
      exact (div_le_one hDpos).mpr (hgD y)
    have hE := abs_lintegral_toReal_sub_le_eventTotalVariation μ ν hkm hk1
    have hconv : ∀ (θ : Measure Y) [IsProbabilityMeasure θ],
        (∫⁻ y, k y ∂θ).toReal = (∫ y, (f y - m) ∂θ) / D := by
      intro θ _
      rw [← integral_div, integral_eq_lintegral_of_nonneg_ae
        (Eventually.of_forall fun y => div_nonneg (hg0 y) hDpos.le)
        (((hf.measurable.sub measurable_const).div_const D).aestronglyMeasurable)]
    rw [hconv μ, hconv ν, ← sub_div, abs_div, abs_of_pos hDpos, div_le_iff₀ hDpos] at hE
    linarith

/-- Two-point law on `ℝ`: mass `1 − ε` at `0` and `ε` at `n`. -/
noncomputable def tailMix (ε : ℝ) (n : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - ε) • Measure.dirac 0 + ENNReal.ofReal ε • Measure.dirac n

theorem tailMix_isProbability {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (n : ℝ) :
    IsProbabilityMeasure (tailMix ε n) := by
  constructor
  simp only [tailMix, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]
  simp

/-- **A3.4 firewall (unbounded metric).** On `ℝ`, for every `ε ∈ (0,1]` and every
constant `C`, some pair has event TV at most `ε` but dual `W₁` above `C ε`: no
TV → W₁ conversion without a diameter bound. -/
theorem tv_does_not_control_w1_on_real {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (C : ℝ) :
    ∃ n : ℕ, (haveI := tailMix_isProbability hε.le hε1 n
      eventTotalVariation (Measure.dirac (0 : ℝ)) (tailMix ε n) ≤ ε) ∧
      ¬ W1DualLE (Measure.dirac (0 : ℝ)) (tailMix ε n) (C * ε) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max C 0)
  have hnC : C < n := (le_max_left _ _).trans_lt hn
  have hn0 : (0 : ℝ) ≤ n := (le_max_right _ _).trans hn.le
  have := tailMix_isProbability hε.le hε1 n
  refine ⟨n, ?_, ?_⟩
  · refine eventTotalVariation_le_of_forall _ _ hε.le fun s hs => ⟨?_, ?_⟩
    · simp only [tailMix, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      by_cases h0 : (0 : ℝ) ∈ s
      · rw [Measure.dirac_apply_of_mem h0]
        calc (1 : ℝ≥0∞) = ENNReal.ofReal (1 - ε) + ENNReal.ofReal ε := by
              rw [← ENNReal.ofReal_add (by linarith) hε.le]; simp
          _ ≤ _ := by
              rw [mul_one, add_assoc]
              exact add_le_add le_rfl le_add_self
      · rw [Measure.dirac_apply' _ hs, Set.indicator_of_notMem h0]; positivity
    · simp only [tailMix, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      gcongr
      · calc ENNReal.ofReal (1 - ε) * Measure.dirac 0 s ≤ 1 * Measure.dirac 0 s := by
              gcongr; rw [ENNReal.ofReal_le_one]; linarith
          _ = _ := one_mul _
      · calc ENNReal.ofReal ε * Measure.dirac (n : ℝ) s ≤ ENNReal.ofReal ε * 1 := by
              gcongr; exact prob_le_one
          _ = _ := mul_one _
  · intro hW
    let f : ℝ → ℝ := fun x => max 0 (min x n)
    have hf : IsKRTest f := by
      refine ⟨by fun_prop, ?_, ⟨n, fun x => ?_⟩⟩
      · exact (LipschitzWith.id.min_const (n : ℝ)).const_max 0
      · simp only [f]
        rw [abs_of_nonneg (le_max_left _ _)]
        exact max_le hn0 (min_le_right _ _)
    have h := hW f hf
    have hint : ∀ x : ℝ, Integrable f (Measure.dirac x) := fun x => hf.integrable _
    simp only [tailMix] at h
    rw [integral_add_measure ((hint 0).smul_measure ENNReal.ofReal_ne_top)
        ((hint n).smul_measure ENNReal.ofReal_ne_top),
      integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac] at h
    simp only [f, min_eq_left hn0, max_eq_left (le_refl (0:ℝ)), max_eq_right hn0,
      min_self, ENNReal.toReal_ofReal hε.le, smul_eq_mul, mul_zero, zero_add,
      zero_sub, abs_neg] at h
    rw [abs_of_nonneg (mul_nonneg hε.le hn0)] at h
    nlinarith

end PermanssonResearch.Probability
