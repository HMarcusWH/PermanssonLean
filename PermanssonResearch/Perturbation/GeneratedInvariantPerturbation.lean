import PermanssonResearch.Perturbation.FirstMomentInvariant

/-! The original perturbation data with both invariant laws genuinely
constructed from moment preservation and the two global contractions. -/

open MeasureTheory ProbabilityTheory TopologicalSpace
namespace PermanssonResearch.Perturbation.FirstMomentInvariant
open PermanssonResearch.Probability
set_option autoImplicit false

variable {Y : Type*} [MetricSpace Y] [CompleteSpace Y] [MeasurableSpace Y]
variable [BorelSpace Y] [SeparableSpace Y]

noncomputable def generatedPerturbation (K Kt : Kernel Y Y) [IsMarkovKernel K]
    [IsMarkovKernel Kt] (y₀ : Y) (hM : PreservesFirstMoment K y₀)
    (hMt : PreservesFirstMoment Kt y₀) {ρ ρt δ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hρt0 : 0 ≤ ρt) (hρt1 : ρt < 1)
    (hK : IsW1Contraction K ρ) (hKt : IsW1Contraction Kt ρt)
    (hδ : ∀ y, W1DualLE (K y) (Kt y) δ) : ContractivePerturbation K Kt where
  π := (stationary K y₀ hM hρ0 hρ1 hK).measure
  πt := (stationary Kt y₀ hMt hρt0 hρt1 hKt).measure
  π_isProb := inferInstance
  πt_isProb := inferInstance
  invariant := stationary_invariant K y₀ hM hρ0 hρ1 hK
  invariant_t := stationary_invariant Kt y₀ hMt hρt0 hρt1 hKt
  ρ := ρ
  δ := δ
  ρ_nonneg := hρ0
  ρ_lt_one := hρ1
  contraction := hK
  defect := hδ
  finite := ⟨_,W1DualLE.of_integrable_dist _ _ y₀
    (stationary K y₀ hM hρ0 hρ1 hK).firstMoment
    (stationary Kt y₀ hMt hρt0 hρt1 hKt).firstMoment⟩

theorem generated_coupling_bound (K Kt : Kernel Y Y) [IsMarkovKernel K]
    [IsMarkovKernel Kt] (y₀ : Y) (hM : PreservesFirstMoment K y₀)
    (hMt : PreservesFirstMoment Kt y₀) {ρ ρt δ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hρt0 : 0 ≤ ρt) (hρt1 : ρt < 1)
    (hK : IsW1Contraction K ρ) (hKt : IsW1Contraction Kt ρt)
    (hδ : ∀ y, W1DualLE (K y) (Kt y) δ) :
    let D := generatedPerturbation K Kt y₀ hM hMt hρ0 hρ1 hρt0 hρt1 hK hKt hδ
    couplingW1 D.π D.πt ≤ δ/(1-ρ) := by
  let D := generatedPerturbation K Kt y₀ hM hMt hρ0 hρ1 hρt0 hρt1 hK hKt hδ
  haveI : IsProbabilityMeasure D.π := D.π_isProb
  haveI : IsProbabilityMeasure D.πt := D.πt_isProb
  exact firstMoment_couplingW1_le_of_w1DualLE D.π D.πt y₀
    (stationary K y₀ hM hρ0 hρ1 hK).firstMoment
    (stationary Kt y₀ hMt hρt0 hρt1 hKt).firstMoment D.w1_le

end PermanssonResearch.Perturbation.FirstMomentInvariant
