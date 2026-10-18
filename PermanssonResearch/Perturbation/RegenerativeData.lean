import PermanssonResearch.Probability.RegenerativePoisson
import PermanssonResearch.Perturbation.ContractiveOccupation
import PermanssonResearch.Probability.FirstMomentKantorovichDuality

/-! Regeneration data with actual generated invariant laws. A baseline
contraction is retained only where the original perturbation theorem needs it. -/

open MeasureTheory ProbabilityTheory TopologicalSpace
namespace PermanssonResearch.Perturbation.RegenerativeFactorization
open PermanssonResearch.Probability PermanssonResearch.Probability.Regenerative
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y]

structure Data (K : Kernel Y Y) where
  residual : Kernel Y Y
  residual_markov : IsMarkovKernel residual
  seed : ProbabilityMeasure Y
  r : ℝ
  r_nonneg : 0 ≤ r
  r_lt_one : r < 1
  mixture : IsMixture residual K seed r

attribute [instance] Data.residual_markov

noncomputable def Data.ofEpsilon (K R : Kernel Y Y) [IsMarkovKernel R]
    (ξ : ProbabilityMeasure Y) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hmix : ∀ y, K y = ENNReal.ofReal ε • ξ.toMeasure + ENNReal.ofReal (1-ε) • R y) :
    Data K where
  residual := R
  residual_markov := inferInstance
  seed := ξ
  r := 1-ε
  r_nonneg := sub_nonneg.mpr hε1
  r_lt_one := by linarith
  mixture := by
    intro y
    have he : (1 : ℝ)-(1-ε) = ε := by ring
    simpa only [he] using hmix y

noncomputable def Data.stationary {K : Kernel Y Y} (D : Data K) : ProbabilityMeasure Y :=
  probabilityLaw D.residual D.seed D.r_nonneg D.r_lt_one

theorem Data.stationary_invariant {K : Kernel Y Y} [IsMarkovKernel K] (D : Data K) :
    Kernel.Invariant K D.stationary.toMeasure :=
  law_invariant D.residual K D.seed D.r_nonneg D.r_lt_one D.mixture

variable [MetricSpace Y] [BorelSpace Y] [SeparableSpace Y]

noncomputable def generatedPerturbation (K Kt : Kernel Y Y) [IsMarkovKernel K]
    [IsMarkovKernel Kt] (D : Data K) (Dt : Data Kt) (y₀ : Y)
    (hπ : Integrable (fun y => dist y y₀) D.stationary.toMeasure)
    (hπt : Integrable (fun y => dist y y₀) Dt.stationary.toMeasure)
    {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : IsW1Contraction K ρ)
    (hδ : ∀ y, W1DualLE (K y) (Kt y) δ) : ContractivePerturbation K Kt where
  π := D.stationary.toMeasure
  πt := Dt.stationary.toMeasure
  π_isProb := inferInstance
  πt_isProb := inferInstance
  invariant := D.stationary_invariant
  invariant_t := Dt.stationary_invariant
  ρ := ρ
  δ := δ
  ρ_nonneg := hρ0
  ρ_lt_one := hρ1
  contraction := hK
  defect := hδ
  finite := ⟨_,W1DualLE.of_integrable_dist _ _ y₀ hπ hπt⟩

theorem generated_coupling_bound (K Kt : Kernel Y Y) [IsMarkovKernel K]
    [IsMarkovKernel Kt] (D : Data K) (Dt : Data Kt) (y₀ : Y)
    (hπ : Integrable (fun y => dist y y₀) D.stationary.toMeasure)
    (hπt : Integrable (fun y => dist y y₀) Dt.stationary.toMeasure)
    {ρ δ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : IsW1Contraction K ρ)
    (hδ : ∀ y, W1DualLE (K y) (Kt y) δ) :
    couplingW1 D.stationary.toMeasure Dt.stationary.toMeasure ≤ δ/(1-ρ) :=
  firstMoment_couplingW1_le_of_w1DualLE _ _ y₀ hπ hπt
    (generatedPerturbation K Kt D Dt y₀ hπ hπt hρ0 hρ1 hK hδ).w1_le

end PermanssonResearch.Perturbation.RegenerativeFactorization
