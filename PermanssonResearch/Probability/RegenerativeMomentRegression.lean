import PermanssonResearch.Perturbation.RegenerativeFirstMomentFactorization
import PermanssonResearch.MultipleLimit.RegenerativeDescriptorTails
import Mathlib.Analysis.SpecificLimits.Normed

/-! A noncompact real-state reset-and-increment chain. Its constructed
invariant law has positive atoms arbitrarily far away, but a finite
regenerative first moment. The descriptor is the unbounded identity map. -/

open MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped Topology ENNReal BoundedContinuousFunction ProbabilityTheory
namespace PermanssonResearch.Probability.RegenerativeMomentRegression
open Regenerative RegenerativeMoment
open MultipleLimit MultipleLimit.FiniteCanonicalPath
open MultipleLimit.RegenerativeDescriptorMoments MultipleLimit.RegenerativeFirstMoment
set_option autoImplicit false

noncomputable def seed : ProbabilityMeasure ℝ := ⟨Measure.dirac 0,inferInstance⟩
noncomputable def increment : Kernel ℝ ℝ := Kernel.deterministic (fun x => x+1) (by fun_prop)
instance increment_markov : IsMarkovKernel increment := by unfold increment; infer_instance

theorem residual_orbit (n : ℕ) : orbitLaw increment seed n = Measure.dirac (n : ℝ) := by
  induction n with
  | zero => simp [orbitLaw,seed]
  | succ n ih =>
    rw [orbitLaw,ih,increment,Measure.deterministic_comp_eq_map,
      Measure.map_dirac' (by fun_prop)]
    simp

noncomputable def resetWalk : Kernel ℝ ℝ :=
  ⟨fun y => ENNReal.ofReal (1/2 : ℝ) • seed.toMeasure + ENNReal.ofReal (1/2 : ℝ) • increment y,
    by
      apply Measure.measurable_of_measurable_coe
      intro E hE
      simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul]
      exact measurable_const.add (measurable_const.mul (increment.measurable_coe hE))⟩

instance resetWalk_markov : IsMarkovKernel resetWalk := by
  constructor
  intro y
  apply isProbabilityMeasure_iff.mpr
  change (ENNReal.ofReal (1/2 : ℝ) • seed.toMeasure +
    ENNReal.ofReal (1/2 : ℝ) • increment y) Set.univ = 1
  simp only [Measure.add_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem resetWalk_mixture : IsMixture increment resetWalk seed (1/2) := by
  intro y
  norm_num [resetWalk]

theorem distance_reward_condition :
    RewardCondition increment seed (1/2) (fun y : ℝ => dist y 0) := by
  have he (n : ℕ) : (∫⁻ y : ℝ, ‖dist y 0‖ₑ ∂orbitLaw increment seed n) =
      ENNReal.ofReal (n : ℝ) := by
    rw [residual_orbit,lintegral_dirac]
    simp only [Real.dist_eq,sub_zero,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n),
      Real.enorm_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  have hs : Summable (fun n : ℕ => (1/2 : ℝ)^n*(n : ℝ)) := by
    simpa only [mul_comm] using
      (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2 : ℝ)) (by norm_num)).summable
  unfold RewardCondition
  simp_rw [he,← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) _)]
  exact hs.tsum_ofReal_lt_top

theorem invariant_atom_positive (n : ℕ) :
    0 < law increment seed (1/2) {(n : ℝ)} := by
  have he := Measure.le_sum
    (fun k : ℕ => ENNReal.ofReal ((1-(1/2 : ℝ))*(1/2 : ℝ)^k) • orbitLaw increment seed k)
    n {(n : ℝ)}
  rw [residual_orbit,Measure.smul_apply] at he
  rw [Measure.dirac_apply_of_mem (Set.mem_singleton _)] at he
  simp only [smul_eq_mul,mul_one] at he
  have hp : 0 < ENNReal.ofReal ((1-(1/2 : ℝ))*(1/2 : ℝ)^n) :=
    ENNReal.ofReal_pos.mpr (by positivity)
  exact hp.trans_le he

theorem invariant_unbounded_support (B : ℝ) :
    ∃ n : ℕ, B < (n : ℝ) ∧ 0 < law increment seed (1/2) {(n : ℝ)} := by
  obtain ⟨n,hn⟩ := exists_nat_gt B
  exact ⟨n,hn,invariant_atom_positive n⟩

noncomputable def targetLaw : FirstMomentProbability (0 : ℝ) :=
  target increment seed (by norm_num) (by norm_num) id measurable_id 0 distance_reward_condition

theorem all_initial_actual_empirical_W1 (μ : ProbabilityMeasure ℝ) :
    ∀ᵐ w ∂canonicalPathLaw resetWalk μ.toMeasure,
      Tendsto (fun n => FirstMomentEmpirical.empirical 0 n w) atTop (𝓝 targetLaw) := by
  simpa only [Function.comp_apply,id_eq] using!
    canonical_descriptor_empirical_tendsto increment resetWalk seed μ
      (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num) resetWalk_mixture
      id measurable_id 0 distance_reward_condition

theorem all_initial_distance_tail_uniform (μ : ProbabilityMeasure ℝ) :
    ∀ᵐ w ∂canonicalPathLaw resetWalk μ.toMeasure, ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n : ℕ,
      (∑ t ∈ Finset.range (n+1), RegenerativeDescriptorTails.tail 0 M (w t))/((n+1 : ℕ) : ℝ) < ε := by
  simpa only [id_eq] using RegenerativeDescriptorTails.canonical_excess_tail_uniform
    increment resetWalk seed μ (show (0 : ℝ) ≤ 1/2 by norm_num) (by norm_num)
      resetWalk_mixture id measurable_id 0 distance_reward_condition

end PermanssonResearch.Probability.RegenerativeMomentRegression
