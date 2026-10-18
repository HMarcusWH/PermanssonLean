import PermanssonResearch.Probability.FirstMomentCompleteness
import PermanssonResearch.Perturbation.ContractiveOccupation

/-! A genuine kernel action on the first-moment class, with an explicit drift
criterion for its moment preservation and the original all-law contraction. -/

open MeasureTheory ProbabilityTheory TopologicalSpace
namespace PermanssonResearch.Perturbation.FirstMomentInvariant
open PermanssonResearch.Probability
set_option autoImplicit false

variable {Y : Type*} [MetricSpace Y] [MeasurableSpace Y] [BorelSpace Y]
variable [SeparableSpace Y]

def PreservesFirstMoment (K : Kernel Y Y) (y₀ : Y) : Prop :=
  ∀ (μ : Measure Y), IsProbabilityMeasure μ → Integrable (fun y => dist y y₀) μ →
    Integrable (fun y => dist y y₀) (K ∘ₘ μ)

theorem preservesFirstMoment_of_drift (K : Kernel Y Y) [IsMarkovKernel K] (y₀ : Y)
    (hrow : ∀ x, Integrable (fun y => dist y y₀) (K x)) (a b : ℝ)
    (hbound : ∀ x, (∫ y, dist y y₀ ∂K x) ≤ a * dist x y₀ + b) :
    PreservesFirstMoment K y₀ := by
  intro μ hprob hμ
  letI : IsProbabilityMeasure μ := hprob
  apply (Measure.integrable_comp_iff
    (measurable_id.dist measurable_const).aestronglyMeasurable).2
  refine ⟨ae_of_all _ hrow,?_⟩
  have hm : StronglyMeasurable (fun x => ∫ y, dist y y₀ ∂K x) :=
    (measurable_id.dist measurable_const).stronglyMeasurable.integral_kernel
  have hi : Integrable (fun x => ∫ y, dist y y₀ ∂K x) μ := by
    apply ((hμ.const_mul a).add (integrable_const b)).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _ => dist_nonneg))]
    exact hbound x
  simpa only [id_eq,Real.norm_of_nonneg dist_nonneg] using hi

noncomputable def push (K : Kernel Y Y) [IsMarkovKernel K] {y₀ : Y}
    (hM : PreservesFirstMoment K y₀) (μ : FirstMomentProbability y₀) :
    FirstMomentProbability y₀ :=
  ⟨⟨K ∘ₘ μ.measure,inferInstance⟩,hM μ.measure inferInstance μ.firstMoment⟩

theorem push_measure (K : Kernel Y Y) [IsMarkovKernel K] {y₀ : Y}
    (hM : PreservesFirstMoment K y₀) (μ : FirstMomentProbability y₀) :
    (push K hM μ).measure = K ∘ₘ μ.measure := rfl

theorem push_lipschitz (K : Kernel Y Y) [IsMarkovKernel K] {y₀ : Y}
    (hM : PreservesFirstMoment K y₀) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hK : IsW1Contraction K ρ) : LipschitzWith ⟨ρ,hρ⟩ (push K hM) := by
  apply LipschitzWith.of_dist_le_mul
  intro μ ν
  apply FirstMomentProbability.distance_le
  exact hK μ.measure ν.measure inferInstance inferInstance (dist μ ν)
    (FirstMomentProbability.dual_distance μ ν)

noncomputable def iterateLaw (K : Kernel Y Y) (μ : Measure Y) : ℕ → Measure Y
  | 0 => μ
  | n+1 => K ∘ₘ iterateLaw K μ n

theorem iterate_push_measure (K : Kernel Y Y) [IsMarkovKernel K] {y₀ : Y}
    (hM : PreservesFirstMoment K y₀) (μ : FirstMomentProbability y₀) (n : ℕ) :
    ((push K hM)^[n] μ).measure = iterateLaw K μ.measure n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply',push_measure,iterateLaw,ih]

end PermanssonResearch.Perturbation.FirstMomentInvariant
