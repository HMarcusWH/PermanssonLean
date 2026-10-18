import PermanssonResearch.Perturbation.RegenerativeOccupationFactorization
import PermanssonResearch.Perturbation.RegenerativeCompactOccupation
import PermanssonResearch.Perturbation.RegenerativeCompactFactorization

/-! Nontrivial regeneration on the noncompact real line, including all
initial laws and a rejected false regeneration decomposition. -/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace PermanssonResearch.Probability.RegenerativeRegression
open PermanssonResearch.Probability.Regenerative
open PermanssonResearch.MultipleLimit.Regenerative
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.FiniteStateOccupation
set_option autoImplicit false

theorem identity_residual_law {Y : Type*} [MeasurableSpace Y]
    (ξ : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    law Kernel.id ξ r = ξ.toMeasure := by
  have ho (n : ℕ) : orbitLaw Kernel.id ξ n = ξ.toMeasure := by
    induction n with
    | zero => rfl
    | succ n ih => simp only [orbitLaw,Measure.id_comp,ih]
  apply Measure.ext
  intro s hs
  rw [law,Measure.sum_apply _ hs]
  simp_rw [Measure.smul_apply,ho,smul_eq_mul]
  rw [ENNReal.tsum_mul_right,geometric_weight_sum hr hr1,one_mul]

noncomputable def seed : ProbabilityMeasure ℝ := ⟨Measure.dirac 0,inferInstance⟩

noncomputable def halfReset : Kernel ℝ ℝ :=
  ⟨fun y => ENNReal.ofReal (1/2 : ℝ) • seed.toMeasure +
      ENNReal.ofReal (1/2 : ℝ) • (Kernel.id : Kernel ℝ ℝ) y,
    by
      apply Measure.measurable_of_measurable_coe
      intro s hs
      simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul]
      exact measurable_const.add
        (measurable_const.mul ((Kernel.id : Kernel ℝ ℝ).measurable_coe hs))⟩

instance halfReset_markov : IsMarkovKernel halfReset := by
  constructor
  intro y
  apply isProbabilityMeasure_iff.mpr
  change (ENNReal.ofReal (1/2 : ℝ) • seed.toMeasure +
    ENNReal.ofReal (1/2 : ℝ) • (Kernel.id : Kernel ℝ ℝ) y) Set.univ = 1
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem halfReset_mixture : IsMixture Kernel.id halfReset seed (1/2) := by
  intro y
  norm_num [halfReset]

theorem halfReset_geometric_law : law Kernel.id seed (1/2) = Measure.dirac (0 : ℝ) :=
  identity_residual_law seed (by norm_num) (by norm_num)

theorem halfReset_all_initial_weak (μ : ProbabilityMeasure ℝ) :
    ∀ᵐ w ∂canonicalPathLaw halfReset μ.toMeasure,
      Tendsto (fun n => empiricalOccupation w (n+1) (Nat.succ_pos n)) atTop (𝓝 seed) := by
  have he : probabilityLaw Kernel.id seed (r := (1/2 : ℝ)) (by norm_num) (by norm_num) = seed := by
    apply ProbabilityMeasure.toMeasure_injective
    exact halfReset_geometric_law
  simpa only [he] using canonical_regenerative_empirical halfReset Kernel.id seed μ
    (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num) halfReset_mixture

theorem halfReset_all_bounded_measurable_averages (μ : ProbabilityMeasure ℝ)
    (f : ℝ → ℝ) (hf : Measurable f) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ y, |f y| ≤ M) :
    ∀ᵐ w ∂canonicalPathLaw halfReset μ.toMeasure,
      Tendsto (fun n => (∑ t ∈ Finset.range (n+1), f (w t))/((n+1 : ℕ) : ℝ))
        atTop (𝓝 (f 0)) := by
  simpa only [halfReset_geometric_law,integral_dirac] using
    canonical_regenerative_averages halfReset Kernel.id seed μ
      (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num) halfReset_mixture hf hM hb

theorem false_reset_decomposition_rejected : ¬ IsMixture Kernel.id Kernel.id seed 0 := by
  intro h
  have he := congrArg (fun m : Measure ℝ => m {3}) (h 3)
  norm_num [Kernel.id,Kernel.deterministic_apply,seed] at he

end PermanssonResearch.Probability.RegenerativeRegression
