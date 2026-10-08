import PermanssonResearch.ConstitutiveQuasi.Definition

/-!
# CQ-1: bounded-expectation stability from common finite-path mass

The stronger generic claim `|E_μ f - E_ν f| ≤ eventTV μ ν`
is not assumed here. We prove the exact factor-one estimate against a
certified common submeasure and combine it with the already-proved
common-prefix mass bound. The geometric estimate has exactly the same
value as the core event-TV bound and covers every measurable f in [0,1].
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace ConstitutiveQuasi

universe uΩ uY
variable {Ω : Type uΩ} [MeasurableSpace Ω]

/-- If ξ is shared probability mass, a bounded score differs by at most
the missing mass. Both measures are probability laws; ξ is finite and
dominated by each. -/
theorem boundedIntegral_abs_le_one_sub_commonMass
    {μ ν ξ : Measure Ω} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsFiniteMeasure ξ]
    (hξμ : ξ ≤ μ) (hξν : ξ ≤ ν)
    (f : Ω → ℝ) (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    |(∫ x, f x ∂μ) - (∫ x, f x ∂ν)| ≤
      1 - ξ.real Set.univ := by
  have hi (ρ : Measure Ω) [IsFiniteMeasure ρ] : Integrable f ρ := by
    refine Integrable.mono' (integrable_const (1 : ℝ))
      hf.aestronglyMeasurable (ae_of_all ρ ?_)
    intro x
    rw [Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    exact h1 x
  have hμf := hi μ
  have hνf := hi ν
  have hξf := hi ξ
  have hμc : Integrable (fun x => 1 - f x) μ :=
    (integrable_const (1 : ℝ)).sub hμf
  have hνc : Integrable (fun x => 1 - f x) ν :=
    (integrable_const (1 : ℝ)).sub hνf
  have hξc : Integrable (fun x => 1 - f x) ξ :=
    (integrable_const (1 : ℝ)).sub hξf
  have hmuf : (∫ x, f x ∂ξ) ≤ (∫ x, f x ∂μ) :=
    integral_mono_measure hξμ (ae_of_all μ h0) hμf
  have hnuf : (∫ x, f x ∂ξ) ≤ (∫ x, f x ∂ν) :=
    integral_mono_measure hξν (ae_of_all ν h0) hνf
  have hmuc : (∫ x, (1 - f x) ∂ξ) ≤
      (∫ x, (1 - f x) ∂μ) :=
    integral_mono_measure hξμ
      (ae_of_all μ (fun x => sub_nonneg.mpr (h1 x))) hμc
  have hnuc : (∫ x, (1 - f x) ∂ξ) ≤
      (∫ x, (1 - f x) ∂ν) :=
    integral_mono_measure hξν
      (ae_of_all ν (fun x => sub_nonneg.mpr (h1 x))) hνc
  have hμsum : (∫ x, f x ∂μ) +
      (∫ x, (1 - f x) ∂μ) = 1 := by
    rw [integral_sub (integrable_const _) hμf]
    simp
  have hνsum : (∫ x, f x ∂ν) +
      (∫ x, (1 - f x) ∂ν) = 1 := by
    rw [integral_sub (integrable_const _) hνf]
    simp
  have hξsum : (∫ x, f x ∂ξ) +
      (∫ x, (1 - f x) ∂ξ) = ξ.real Set.univ := by
    rw [integral_sub (integrable_const _) hξf]
    simp
  rw [abs_le]
  constructor <;> linarith

variable {Y : Type uY} [MeasurableSpace Y]

/-- Geometric finite-horizon perturbation budget for any measurable [0,1]
score, from the exact common-prefix kernel formalized in the frozen core. -/
theorem finitePathExpectation_abs_le_geometric
    [MeasurableSpace.CountableOrCountablyGenerated Y Y]
    (K Ktilde : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel Ktilde]
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hTV : PermanssonLean.ProbabilitySupport.HasUniformEventTVBound K Ktilde δ)
    (y : Y) (L : ℕ) (f : FinitePathProperty Y L) :
    |f.fromKernel L K y - f.fromKernel L Ktilde y| ≤
      PermanssonLean.ProbabilitySupport.geometricTVEnvelope δ L := by
  let ξ := PermanssonLean.ProbabilitySupport.commonFinitePrefixLaw K Ktilde y L
  have hcommon := boundedIntegral_abs_le_one_sub_commonMass
    (μ := PermanssonLean.ProbabilitySupport.finitePrefixLaw K y L)
    (ν := PermanssonLean.ProbabilitySupport.finitePrefixLaw Ktilde y L)
    (ξ := ξ)
    (PermanssonLean.ProbabilitySupport.commonFinitePrefixLaw_le_left K Ktilde y L)
    (PermanssonLean.ProbabilitySupport.commonFinitePrefixLaw_le_right K Ktilde y L)
    f.score f.measurable_score f.score_nonneg f.score_le_one
  have hmass :=
    PermanssonLean.ProbabilitySupport.commonFinitePrefixLaw_real_univ_ge_pow
      K Ktilde hδ1 hTV y L
  unfold PermanssonLean.ProbabilitySupport.geometricTVEnvelope
  dsimp [FinitePathProperty.fromKernel, FinitePathProperty.expected] at *
  linarith

end ConstitutiveQuasi
end PermanssonResearch
