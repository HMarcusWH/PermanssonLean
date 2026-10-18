import PermanssonResearch.Probability.EventTVCalculus
import PermanssonLean.Probability.FinitePrefixTV
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-! Retained common mass for genuinely dependent history types and
time-varying kernels. The recursion constructs a common submeasure;
no recurrence for the actual total-variation discrepancy is assumed. -/

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal ProbabilityTheory
namespace PermanssonResearch.Probability.DependentHistory
open PermanssonLean.ProbabilitySupport
set_option autoImplicit false

universe u
variable {H : ℕ → Type u} [∀ n, MeasurableSpace (H n)]

noncomputable def evolution (μ : Measure (H 0))
    (K : ∀ n, Kernel (H n) (H (n+1))) : ∀ n, Measure (H n)
  | 0 => μ
  | n+1 => (evolution μ K n ⊗ₘ K n).map Prod.snd

theorem evolution_probability (μ : Measure (H 0)) [IsProbabilityMeasure μ]
    (K : ∀ n, Kernel (H n) (H (n+1))) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsProbabilityMeasure (evolution μ K n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih =>
    letI := ih
    exact (Measure.isProbabilityMeasure_map_iff measurable_snd.aemeasurable).mpr inferInstance

theorem evolution_finite (μ : Measure (H 0)) [IsFiniteMeasure μ]
    (K : ∀ n, Kernel (H n) (H (n+1))) [∀ n, IsFiniteKernel (K n)] (n : ℕ) :
    IsFiniteMeasure (evolution μ K n) := by
  induction n with
  | zero => exact inferInstanceAs (IsFiniteMeasure μ)
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (IsFiniteMeasure ((evolution μ K n ⊗ₘ K n).map Prod.snd))

theorem compProd_mono {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ ν : Measure A} [SFinite μ] [SFinite ν]
    {R K : Kernel A B} [IsSFiniteKernel R] [IsSFiniteKernel K]
    (hμ : μ ≤ ν) (hR : R ≤ K) : μ ⊗ₘ R ≤ ν ⊗ₘ K := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.compProd_apply hE,Measure.compProd_apply hE]
  exact lintegral_mono' hμ (fun h => hR h _)

theorem evolution_mono {ξ μ : Measure (H 0)} [IsFiniteMeasure ξ] [IsFiniteMeasure μ]
    (R K : ∀ n, Kernel (H n) (H (n+1)))
    [∀ n, IsFiniteKernel (R n)] [∀ n, IsFiniteKernel (K n)]
    (hξ : ξ ≤ μ) (hR : ∀ n, R n ≤ K n) (n : ℕ) :
    evolution ξ R n ≤ evolution μ K n := by
  induction n with
  | zero => exact hξ
  | succ n ih =>
    haveI := evolution_finite ξ R n
    haveI := evolution_finite μ K n
    exact Measure.map_mono (compProd_mono ih (hR n)) measurable_snd

def retained (η : ℕ → ℝ) (n : ℕ) : ℝ := ∏ t ∈ range n, (1-η t)

theorem retained_nonneg (η : ℕ → ℝ) (hη1 : ∀ n, η n ≤ 1) (n : ℕ) :
    0 ≤ retained η n := prod_nonneg fun t _ => sub_nonneg.mpr (hη1 t)

theorem retained_le_one (η : ℕ → ℝ) (hη0 : ∀ n, 0 ≤ η n)
    (hη1 : ∀ n, η n ≤ 1) (n : ℕ) : retained η n ≤ 1 := by
  apply prod_le_one₀
  · intro t _; exact sub_nonneg.mpr (hη1 t)
  · intro t _; linarith [hη0 t]

theorem common_mass_ge (ξ : Measure (H 0)) [IsFiniteMeasure ξ]
    (R : ∀ n, Kernel (H n) (H (n+1))) [∀ n, IsFiniteKernel (R n)]
    (η : ℕ → ℝ) (hη1 : ∀ n, η n ≤ 1)
    (hmass : ∀ n h, ENNReal.ofReal (1-η n) ≤ R n h univ)
    {ε : ℝ} (hε1 : ε ≤ 1) (hξmass : ENNReal.ofReal (1-ε) ≤ ξ univ) (n : ℕ) :
    ENNReal.ofReal ((1-ε)*retained η n) ≤ evolution ξ R n univ := by
  induction n with
  | zero => simpa [evolution,retained] using hξmass
  | succ n ih =>
    haveI := evolution_finite ξ R n
    have hη : 0 ≤ 1-η n := sub_nonneg.mpr (hη1 n)
    have hbase : 0 ≤ (1-ε)*retained η n :=
      mul_nonneg (sub_nonneg.mpr hε1) (retained_nonneg η hη1 n)
    rw [evolution,Measure.map_apply measurable_snd MeasurableSet.univ]
    simp only [preimage_univ]
    rw [Measure.compProd_apply MeasurableSet.univ]
    simp only [preimage_univ]
    calc
      ENNReal.ofReal ((1-ε)*retained η (n+1)) =
          ENNReal.ofReal (1-η n)*ENNReal.ofReal ((1-ε)*retained η n) := by
        rw [retained,prod_range_succ]
        change ENNReal.ofReal ((1-ε)*(retained η n*(1-η n))) = _
        rw [← mul_assoc,ENNReal.ofReal_mul hbase,mul_comm]
      _ ≤ ENNReal.ofReal (1-η n)*evolution ξ R n univ :=
        mul_le_mul_of_nonneg_left ih (by exact bot_le)
      _ = ∫⁻ _h, ENNReal.ofReal (1-η n) ∂evolution ξ R n := by simp
      _ ≤ ∫⁻ h, R n h univ ∂evolution ξ R n := lintegral_mono (hmass n)

theorem prefix_tv_le_product (μ ν ξ : Measure (H 0))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (K L R : ∀ n, Kernel (H n) (H (n+1)))
    [∀ n, IsMarkovKernel (K n)] [∀ n, IsMarkovKernel (L n)]
    [∀ n, IsFiniteKernel (R n)]
    (hξμ : ξ ≤ μ) (hξν : ξ ≤ ν)
    (hRK : ∀ n, R n ≤ K n) (hRL : ∀ n, R n ≤ L n)
    (η : ℕ → ℝ) (hη1 : ∀ n, η n ≤ 1)
    (hmass : ∀ n h, ENNReal.ofReal (1-η n) ≤ R n h univ)
    {ε : ℝ} (hε1 : ε ≤ 1) (hξmass : ENNReal.ofReal (1-ε) ≤ ξ univ) (n : ℕ) :
    eventTotalVariation (evolution μ K n) (evolution ν L n) ≤
      1-(1-ε)*retained η n := by
  letI : IsFiniteMeasure ξ := isFiniteMeasure_of_le μ hξμ
  haveI := evolution_finite ξ R n
  haveI := evolution_probability μ K n
  haveI := evolution_probability ν L n
  have hleft := evolution_mono R K hξμ hRK n
  have hright := evolution_mono R L hξν hRL n
  have htv := eventTotalVariation_le_one_sub_commonMass hleft hright
  have hbound := common_mass_ge ξ R η hη1 hmass hε1 hξmass n
  have hreal := (ENNReal.ofReal_le_iff_le_toReal
    (measure_ne_top (evolution ξ R n) univ)).mp hbound
  exact htv.trans (sub_le_sub_left hreal 1)

end PermanssonResearch.Probability.DependentHistory
