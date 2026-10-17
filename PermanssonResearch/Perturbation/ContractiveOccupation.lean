import PermanssonResearch.Probability.KantorovichDual
import PermanssonLean.Regime.Perturbation
import PermanssonLean.Regime.ConstitutiveMargin

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory


/-!
# A3.1–A3.2 — Contractive invariant-law perturbation and margin robustness

* (V20.17) `invariantLaw_wasserstein_le`: invariant laws `π = Kπ`, `π̃ = K̃π̃`, a
  uniform `W₁` contraction `K` with `0 ≤ ρ < 1`, a one-step defect
  `sup_y W₁(K_y, K̃_y) ≤ δ` and a finite initial gap give `W₁(π, π̃) ≤ δ/(1−ρ)`
  (dual form). Proof: one-step recursion `c ↦ ρc + δ`, iteration, closure — no
  completeness or fixed-point theorem.
* (V20.18) `occupationMargin_robust`: if the property FACTORS as `F(h_#π)` for all
  four compared processes on every comparison state, with `h` `L_h`-Lipschitz and
  `F` `L_F`-Lipschitz for dual `W₁`, the ORIGINAL frozen constitutive margins differ
  by at most `L_F L_h (δ₀/(1−ρ₀) + δ_J/(1−ρ_J))`.

Invariance, contraction, defect, finiteness and the factorization identity are
HYPOTHESES (existence/uniqueness of invariant laws, Doeblin/Dobrushin derivations
of contraction and an ergodic bridge are not formalized). A3.3 shows the
conclusion fails for exact-survival properties.
-/

namespace PermanssonResearch.Perturbation

set_option autoImplicit false

open PermanssonResearch.Probability

universe uY
variable {Y : Type uY} [PseudoMetricSpace Y] [MeasurableSpace Y]

/-- Uniform `W₁` contraction in dual form: `W₁(μK, νK) ≤ ρ W₁(μ, ν)` for all
probability laws. -/
def IsW1Contraction (K : Kernel Y Y) (ρ : ℝ) : Prop :=
  ∀ (μ ν : Measure Y), IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    ∀ c : ℝ, W1DualLE μ ν c → W1DualLE (K ∘ₘ μ) (K ∘ₘ ν) (ρ * c)

/-- One step of the perturbation recursion:
`W(π, π̃) ≤ c ⇒ W(π, π̃) ≤ ρ c + δ`. -/
theorem invariantLaw_step (K Kt : Kernel Y Y) [IsMarkovKernel K] [IsMarkovKernel Kt]
    (π πt : Measure Y) [IsProbabilityMeasure π] [IsProbabilityMeasure πt]
    (hπ : K ∘ₘ π = π) (hπt : Kt ∘ₘ πt = πt) {ρ δ : ℝ}
    (hK : IsW1Contraction K ρ) (hδ : ∀ y, W1DualLE (K y) (Kt y) δ)
    {c : ℝ} (hc : W1DualLE π πt c) : W1DualLE π πt (ρ * c + δ) := by
  have h1 := hK π πt inferInstance inferInstance c hc
  have h2 := W1DualLE.comp_of_forall πt K Kt hδ
  have h3 := h1.trans h2
  rwa [hπ, hπt] at h3

/-- **A3.1 / (V20.17).** Invariant-law perturbation under uniform `W₁`
contraction: `W₁(π, π̃) ≤ δ / (1 − ρ)`. The finiteness hypothesis `hfin` holds
whenever both laws have finite first moments (`W1DualLE.of_integrable_dist`). -/
theorem invariantLaw_wasserstein_le (K Kt : Kernel Y Y) [IsMarkovKernel K]
    [IsMarkovKernel Kt] (π πt : Measure Y) [IsProbabilityMeasure π]
    [IsProbabilityMeasure πt] (hπ : K ∘ₘ π = π) (hπt : Kt ∘ₘ πt = πt) {ρ δ : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hK : IsW1Contraction K ρ)
    (hδ : ∀ y, W1DualLE (K y) (Kt y) δ) (hfin : ∃ c, W1DualLE π πt c) :
    W1DualLE π πt (δ / (1 - ρ)) := by
  obtain ⟨c, hc⟩ := hfin
  set L := δ / (1 - ρ) with hLdef
  have h1ρ : (1 - ρ) ≠ 0 := (sub_pos.mpr hρ1).ne'
  have hfix : ρ * L + δ = L := by
    rw [hLdef]; field_simp; ring
  have hiter : ∀ n : ℕ, W1DualLE π πt (ρ ^ n * (c - L) + L) := by
    intro n
    induction n with
    | zero => simpa using hc
    | succ n ih =>
        have := invariantLaw_step K Kt π πt hπ hπt hK hδ ih
        convert this using 1
        rw [pow_succ]
        nlinarith [hfix]
  refine W1DualLE.of_tendsto hiter ?_
  have hpow : Tendsto (fun n : ℕ => ρ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  simpa using (hpow.mul_const (c - L)).add_const L


/-- Per-protocol data for A3.1: invariant laws of the original and perturbed
kernels, contraction of the ORIGINAL kernel, the one-step defect at every state,
and finiteness of the initial gap. -/
structure ContractivePerturbation (K Kt : Kernel Y Y) where
  π : Measure Y
  πt : Measure Y
  π_isProb : IsProbabilityMeasure π
  πt_isProb : IsProbabilityMeasure πt
  invariant : K ∘ₘ π = π
  invariant_t : Kt ∘ₘ πt = πt
  ρ : ℝ
  δ : ℝ
  ρ_nonneg : 0 ≤ ρ
  ρ_lt_one : ρ < 1
  contraction : IsW1Contraction K ρ
  defect : ∀ y, W1DualLE (K y) (Kt y) δ
  finite : ∃ c, W1DualLE π πt c

namespace ContractivePerturbation

variable {K Kt : Kernel Y Y}

/-- The A3.1 conclusion for the bundled data. -/
theorem w1_le [IsMarkovKernel K] [IsMarkovKernel Kt] (D : ContractivePerturbation K Kt) :
    W1DualLE D.π D.πt (D.δ / (1 - D.ρ)) := by
  have := D.π_isProb; have := D.πt_isProb
  exact invariantLaw_wasserstein_le K Kt D.π D.πt D.invariant D.invariant_t D.ρ_nonneg
    D.ρ_lt_one D.contraction D.defect D.finite

/-- The perturbation budget `δ / (1 − ρ)` is nonnegative. -/
theorem budget_nonneg [IsMarkovKernel K] [IsMarkovKernel Kt]
    (D : ContractivePerturbation K Kt) : 0 ≤ D.δ / (1 - D.ρ) :=
  D.w1_le.nonneg

end ContractivePerturbation

/-- An `L_F`-Lipschitz functional of laws on a metric descriptor space, for the
dual `W₁` bound. -/
def IsW1LipschitzFunctional {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V]
    {Z : Type*} [PseudoMetricSpace Z] (Φ : Measure V → Z) (LF : ℝ) : Prop :=
  ∀ μ ν : Measure V, IsProbabilityMeasure μ → IsProbabilityMeasure ν →
    ∀ c : ℝ, W1DualLE μ ν c → dist (Φ μ) (Φ ν) ≤ LF * c

/-- **A3.2 (output-law step).** `dist(F(h_#π), F(h_#π̃)) ≤ L_F L_h δ/(1−ρ)`. -/
theorem descriptorFunctional_dist_le {K Kt : Kernel Y Y} [IsMarkovKernel K]
    [IsMarkovKernel Kt] (D : ContractivePerturbation K Kt)
    {V : Type*} [PseudoMetricSpace V] [MeasurableSpace V] {Z : Type*} [PseudoMetricSpace Z]
    {h : Y → V} (hh : Measurable h) {Lh : ℝ≥0} (hLh : LipschitzWith Lh h)
    {Φ : Measure V → Z} {LF : ℝ} (hΦ : IsW1LipschitzFunctional Φ LF) :
    dist (Φ (D.π.map h)) (Φ (D.πt.map h)) ≤ LF * Lh * (D.δ / (1 - D.ρ)) := by
  have := D.π_isProb; have := D.πt_isProb
  have hW := D.w1_le.map_lipschitz hh hLh
  have := hΦ _ _ inferInstance
    inferInstance _ hW
  simpa [mul_assoc] using this

end PermanssonResearch.Perturbation

namespace PermanssonResearch.Perturbation

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification PermanssonResearch.Probability

universe uS uX uA uH uH' uZ uC uC' uV

/-- **A3.2 / (V20.18).** Margin robustness for properties that FACTOR through a
Lipschitz functional of the descriptor image of the invariant law, for all
four compared processes and every comparison state:
`|κ̃ − κ| ≤ L_F L_h (δ₀/(1−ρ₀) + δ_J/(1−ρ_J))`. Both margins are the ORIGINAL
frozen constitutive margins over the same comparison states. -/
theorem occupationMargin_robust
    {S : Type uS} {X : Type uX} {A : Type uA} {H : Type uH} {H' : Type uH'} {Z : Type uZ}
    [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
    [MeasurableSpace H'] [PseudoMetricSpace S] [PseudoMetricSpace X] [MetricSpace Z]
    {V : Type uV} [PseudoMetricSpace V] [MeasurableSpace V]
    (M Mt : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (spect : RegimeSpecification (JointState S X) H')
    {C : Type uC} {C' : Type uC'} (F : InterventionFamily M C) (Ft : InterventionFamily Mt C')
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec) (Bt₁ : ConstitutiveComparisonSet Mt spect)
    (hB : Bt₁.states = B₁.states)
    (J : AdmissibleStrategicIntervention F) (Jt : AdmissibleStrategicIntervention Ft)
    (D₀ : @ContractivePerturbation (JointState S X) _ _ M.inducedKernel Mt.inducedKernel)
    (DJ : @ContractivePerturbation (JointState S X) _ _ J.intervention.apply.inducedKernel
      Jt.intervention.apply.inducedKernel)
    {h : JointState S X → V} (hh : Measurable h) {Lh : ℝ≥0} (hLh : LipschitzWith Lh h)
    {Φ : Measure V → Z} {LF : ℝ} (hΦ : IsW1LipschitzFunctional Φ LF)
    (hfac : ∀ y ∈ B₁.states,
      baselinePropertyValue ψ M y = Φ (D₀.π.map h) ∧
      intervenedPropertyValue ψ J.intervention y = Φ (DJ.π.map h) ∧
      baselinePropertyValue ψ Mt y = Φ (D₀.πt.map h) ∧
      intervenedPropertyValue ψ Jt.intervention y = Φ (DJ.πt.map h)) :
    |constitutiveMargin Mt spect Ft ψ Bt₁ Jt - constitutiveMargin M spec F ψ B₁ J| ≤
      LF * Lh * (D₀.δ / (1 - D₀.ρ) + DJ.δ / (1 - DJ.ρ)) := by
  have := StrategicWorldModel.inducedKernel_isMarkov M
  have := StrategicWorldModel.inducedKernel_isMarkov Mt
  have := StrategicWorldModel.inducedKernel_isMarkov J.intervention.apply
  have := StrategicWorldModel.inducedKernel_isMarkov Jt.intervention.apply
  have e₀ := descriptorFunctional_dist_le D₀ hh hLh hΦ
  have eJ := descriptorFunctional_dist_le DJ hh hLh hΦ
  obtain ⟨y₁, hy₁, -⟩ := B₁.pathLawNontrivial
  unfold constitutiveMargin
  rw [hB]
  refine abs_sInf_image_sub_sInf_image_le_of_uniform B₁.states ⟨y₁, hy₁⟩ _ _
    (fun y _ => constitutiveEffect_nonneg Mt ψ Jt y)
    (fun y _ => constitutiveEffect_nonneg M ψ J y) (fun y hy => ?_)
  obtain ⟨h0, hJ, ht0, htJ⟩ := hfac y hy
  unfold constitutiveEffect
  rw [h0, hJ, ht0, htJ]
  set a0 := Φ (D₀.π.map h); set aJ := Φ (DJ.π.map h)
  set b0 := Φ (D₀.πt.map h); set bJ := Φ (DJ.πt.map h)
  have t1 := dist_triangle b0 a0 bJ
  have t2 := dist_triangle a0 aJ bJ
  have t3 := dist_triangle a0 b0 aJ
  have t4 := dist_triangle b0 bJ aJ
  rw [dist_comm b0 a0] at t1
  rw [dist_comm bJ aJ] at t4
  rw [abs_sub_le_iff, mul_add]
  constructor <;> linarith [dist_comm aJ bJ]

end PermanssonResearch.Perturbation
