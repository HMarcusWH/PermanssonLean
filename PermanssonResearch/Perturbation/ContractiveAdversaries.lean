import PermanssonResearch.Perturbation.ContractiveOccupation
import PermanssonLean.Regime.SurvivalBridge
import PermanssonLean.Regime.Persistence

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ProbabilityTheory


/-!
# A3.3 — Contraction does not transfer exact survival

On actual `StrategicWorldModel`s with state space `Unit × ℝ` and a constant world
law (`δ₀` versus `(1−ε)δ₀ + εδ₁`), both induced kernels are `W₁` contractions with
`ρ = 0` and the one-step dual `W₁` defect is at most `ε` at every state, yet the
probability of never leaving `B = {x = 0}` from `y₀` is `1` versus `0`, for every
`ε ∈ (0,1]` (`contraction_does_not_transfer_survival`). Survival is computed with
the frozen killed-kernel bridge (`survivalProbability_eq_killedSurvivalMass`) and
continuity from above. So (V20.18) is NOT a theorem for infinite-path
exact-survival indicator properties.
-/

namespace PermanssonResearch.Perturbation.ContractiveLeak

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification PermanssonResearch.Probability

/-- State space `Unit × ℝ` (product metric); only `x ∈ {0, 1}` is visited. -/
abbrev Yl := JointState Unit ℝ

def y0 : Yl := ((), 0)
def y1 : Yl := ((), 1)

/-- Embedding of the world coordinate. -/
def emb (x : ℝ) : Yl := ((), x)

theorem measurable_emb : Measurable emb := measurable_const.prodMk measurable_id

/-- Leaky world law: `(1 − ε) δ₀ + ε δ₁`. -/
noncomputable def leakLaw (ε : ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 - ε) • Measure.dirac 0 + ENNReal.ofReal ε • Measure.dirac 1

theorem leakLaw_isProbability {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (leakLaw ε) := by
  constructor
  simp only [leakLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add (by linarith) h0]
  simp

/-- Model with trivial strategic layer and a CONSTANT world law `ν`. -/
noncomputable def model (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    StrategicWorldModel Unit ℝ Unit where
  generator :=
    { action := Kernel.const _ (Measure.dirac ())
      update := Kernel.const _ (Measure.dirac ())
      action_isMarkov := inferInstance
      update_isMarkov := inferInstance }
  world := Kernel.const _ ν
  world_isMarkov := inferInstance

theorem model_inducedKernel (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (model ν).inducedKernel = Kernel.const Yl (ν.map emb) := by
  ext y E hE
  rw [StrategicWorldModel.inducedKernel_apply _ y hE, Kernel.const_apply,
    Measure.map_apply measurable_emb hE]
  simp only [model, Kernel.const_apply, lintegral_dirac]
  have hpre : MeasurableSet (emb ⁻¹' E) := measurable_emb hE
  rw [← lintegral_indicator_one hpre]
  congr 1
  funext x
  rw [Measure.dirac_apply]
  by_cases hx : ((), x) ∈ E
  · simp [Set.indicator, hx, emb]
  · simp [Set.indicator, hx, emb]

/-- Regime `B = {y | y.2 = 0}` (basin = region). Descriptor, target and
convergence mode are irrelevant to survival and are fixed trivially. -/
noncomputable def specZero : RegimeSpecification Yl Yl where
  region := {y | y.2 = 0}
  region_measurable := (measurableSet_singleton (0 : ℝ)).preimage measurable_snd
  basin := {y | y.2 = 0}
  basin_measurable := (measurableSet_singleton (0 : ℝ)).preimage measurable_snd
  basin_subset_region := subset_rfl
  descriptor := id
  descriptor_measurable := measurable_id
  target := ⟨Measure.dirac y0, inferInstance⟩
  convergenceMode := ⟨fun _ _ _ => True⟩

theorem y0_mem_region : y0 ∈ specZero.region := rfl

/-- The killed kernel of a constant-world model is `ν{0} · δ_{y0}` restricted. -/
theorem killedKernel_apply_model (ν : Measure ℝ) [IsProbabilityMeasure ν] (z : Yl)
    {C : Set Yl} (hC : MeasurableSet C) :
    killedKernel (model ν) specZero z C = ν {0} * (Measure.dirac y0) C := by
  rw [killedKernel_apply _ _ z hC, model_inducedKernel, Kernel.const_apply,
    Measure.map_apply measurable_emb (hC.inter specZero.region_measurable),
    Measure.dirac_apply' _ hC]
  by_cases h : y0 ∈ C
  · have : emb ⁻¹' (C ∩ specZero.region) = {0} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_singleton_iff, emb, specZero]
      constructor
      · rintro ⟨-, hx⟩; exact hx
      · rintro rfl; exact ⟨h, rfl⟩
    rw [this, Set.indicator_of_mem h, Pi.one_apply, mul_one]
  · have : emb ⁻¹' (C ∩ specZero.region) = ∅ := by
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false,
        not_and, emb, specZero]
      intro hx hx0
      subst hx0
      exact h hx
    rw [this, measure_empty, Set.indicator_of_notMem h, mul_zero]

theorem killedPow_model (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    ((killedKernel (model ν) specZero) ^ n) y0 = (ν {0}) ^ n • Measure.dirac y0 := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, one_smul]
      rfl
  | succ n ih =>
      ext C hC
      rw [Kernel.pow_succ_apply_eq_lintegral _ n y0 hC, ih]
      simp_rw [killedKernel_apply_model ν _ hC]
      rw [lintegral_const, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one,
        Measure.smul_apply, smul_eq_mul, pow_succ]
      ring

theorem survivalProbability_model (ν : Measure ℝ) [IsProbabilityMeasure ν] (n : ℕ) :
    survivalProbability (model ν) specZero y0 n = (ν {0}) ^ n := by
  rw [survivalProbability_eq_killedSurvivalMass _ _ n y0_mem_region, killedSurvivalMass,
    killedPow_model, Measure.smul_apply, Measure.dirac_apply_of_mem y0_mem_region,
    smul_eq_mul, mul_one]

theorem survivalForever_model (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    survivalForeverProbability (model ν) specZero y0 = ⨅ n : ℕ, (ν {0}) ^ n := by
  have := StrategicWorldModel.inducedKernel_isMarkov (model ν)
  let P := (model ν).pathLaw (Measure.dirac y0)
  have hmeas : ∀ n : ℕ, NullMeasurableSet (survivesThroughSet specZero n) P :=
    fun n => (measurableSet_survivesThroughSet specZero n).nullMeasurableSet
  have hfin : ∃ n : ℕ, P (survivesThroughSet specZero n) ≠ ⊤ := ⟨0, measure_ne_top P _⟩
  have h := (survivesThroughSet_antitone specZero).measure_iInter (μ := P) hmeas hfin
  unfold survivalForeverProbability
  rw [survivesForeverSet_eq_iInter]
  change P _ = _
  rw [h]
  congr 1
  funext n
  exact survivalProbability_model ν n

/-- Fine kernel: the world stays at `0`. -/
noncomputable def fineLaw : Measure ℝ := Measure.dirac 0

instance fineLaw_isProbability : IsProbabilityMeasure fineLaw := by
  unfold fineLaw; infer_instance

/-- **A3.3, survival under the fine model:** `P₀(τ_B = ∞) = 1`. -/
theorem fine_survivalForever :
    survivalForeverProbability (model fineLaw) specZero y0 = 1 := by
  rw [survivalForever_model]
  simp [fineLaw]

/-- **A3.3, survival under the leaky model:** `P₀(τ_B = ∞) = 0` for every `ε > 0`. -/
theorem leak_survivalForever {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    haveI := leakLaw_isProbability hε.le hε1
    survivalForeverProbability (model (leakLaw ε)) specZero y0 = 0 := by
  have := leakLaw_isProbability hε.le hε1
  rw [survivalForever_model]
  have hq : leakLaw ε {0} = ENNReal.ofReal (1 - ε) := by
    simp [leakLaw, Measure.dirac_apply_of_mem (Set.mem_singleton (0 : ℝ))]
  rw [hq]
  have hlt : ENNReal.ofReal (1 - ε) < 1 := by
    rw [ENNReal.ofReal_lt_one]; linarith
  exact le_antisymm (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt)
    fun n => iInf_le _ n) bot_le

/-- A constant kernel is a `W₁` contraction with `ρ = 0`. -/
theorem const_isW1Contraction (ν : Measure Yl) [IsProbabilityMeasure ν] :
    IsW1Contraction (Kernel.const Yl ν) 0 := by
  intro μ μ' hμ hμ' c _
  rw [Measure.const_comp, Measure.const_comp, measure_univ, measure_univ, one_smul]
  simpa using W1DualLE.refl ν

theorem dist_y0_y1 : dist y0 y1 = 1 := by
  simp [y0, y1, Prod.dist_eq, Real.dist_eq]

/-- One-step dual `W₁` defect between the fine and leaky rows is at most `ε`. -/
theorem leak_defect {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    W1DualLE (fineLaw.map emb) ((leakLaw ε).map emb) ε := by
  intro f hf
  rw [integral_map measurable_emb.aemeasurable hf.measurable.aestronglyMeasurable,
    integral_map measurable_emb.aemeasurable hf.measurable.aestronglyMeasurable]
  obtain ⟨C, hC⟩ := hf.bounded
  have hc : ∀ x : ℝ, Integrable (fun x => f (emb x)) (Measure.dirac x) := fun x =>
    Integrable.of_bound (hf.measurable.comp measurable_emb).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by simpa [Real.norm_eq_abs] using hC (emb z))
  simp only [fineLaw, leakLaw]
  rw [integral_add_measure ((hc 0).smul_measure ENNReal.ofReal_ne_top)
      ((hc 1).smul_measure ENNReal.ofReal_ne_top), integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac,
    ENNReal.toReal_ofReal (by linarith), ENNReal.toReal_ofReal hε, smul_eq_mul, smul_eq_mul]
  have hL := hf.lipschitz.dist_le_mul y0 y1
  rw [dist_y0_y1, Real.dist_eq] at hL
  simp only [NNReal.coe_one, mul_one] at hL
  have : f (emb 0) - ((1 - ε) * f (emb 0) + ε * f (emb 1)) = ε * (f y0 - f y1) := by
    simp only [emb, y0, y1]; ring
  rw [this, abs_mul, abs_of_nonneg hε]
  nlinarith [abs_nonneg (f y0 - f y1)]

/-- **A3.3 (firewall).** For every `ε ∈ (0,1]` the fine and leaky kernels satisfy
the A3.1 hypotheses with `ρ = 0` (both constant, hence `W₁` contractions) and
one-step dual `W₁` defect `≤ ε` at every state, yet the exact-survival indicator
of `B = {x = 0}` from `y₀` is `1` for the fine model and `0` for the leaky one.
So (V20.18) is NOT a theorem for infinite-path exact-survival properties. -/
theorem contraction_does_not_transfer_survival {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    haveI := leakLaw_isProbability hε.le hε1
    IsW1Contraction (model fineLaw).inducedKernel 0 ∧
      IsW1Contraction (model (leakLaw ε)).inducedKernel 0 ∧
      (∀ y, W1DualLE ((model fineLaw).inducedKernel y)
        ((model (leakLaw ε)).inducedKernel y) ε) ∧
      survivalForeverProbability (model fineLaw) specZero y0 = 1 ∧
      survivalForeverProbability (model (leakLaw ε)) specZero y0 = 0 := by
  have := leakLaw_isProbability hε.le hε1
  refine ⟨?_, ?_, fun y => ?_, fine_survivalForever, leak_survivalForever hε hε1⟩
  · rw [model_inducedKernel]; exact const_isW1Contraction _
  · rw [model_inducedKernel]; exact const_isW1Contraction _
  · rw [model_inducedKernel, model_inducedKernel, Kernel.const_apply, Kernel.const_apply]
    exact leak_defect hε.le hε1

end PermanssonResearch.Perturbation.ContractiveLeak
