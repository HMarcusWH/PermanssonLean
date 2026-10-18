import PermanssonResearch.Probability.RegenerativePoisson
import PermanssonResearch.Probability.EventTVCalculus
import PermanssonLean.Probability.FinitePrefixTV

/-! Regeneration injects a new common seed at every transition. The
constructed common state law has mass 1-r^n and is dominated by the
actual n-th law from every initial probability and by the invariant law. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory
namespace PermanssonResearch.Probability.RegenerativeRenewal
open PermanssonLean.ProbabilitySupport Regenerative
set_option autoImplicit false
variable {Y : Type*} [MeasurableSpace Y]

theorem comp_mono (K : Kernel Y Y) {μ ν : Measure Y} (h : μ ≤ ν) :
    K ∘ₘ μ ≤ K ∘ₘ ν := by
  apply Measure.le_iff.mpr
  intro E hE
  rw [Measure.bind_apply hE K.aemeasurable,Measure.bind_apply hE K.aemeasurable]
  exact lintegral_mono' h (fun _ => le_rfl)

theorem smul_mono_measure (c : ℝ≥0∞) {μ ν : Measure Y} (h : μ ≤ ν) : c • μ ≤ c • ν := by
  intro E
  simp only [Measure.smul_apply,smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (h E) (by exact bot_le)

theorem comp_mixture (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ : ProbabilityMeasure Y) {r : ℝ} (hmix : IsMixture R K ξ r)
    (μ : Measure Y) [IsProbabilityMeasure μ] :
    K ∘ₘ μ = ENNReal.ofReal (1-r) • ξ.toMeasure + ENNReal.ofReal r • (R ∘ₘ μ) := by
  apply Measure.ext
  intro E hE
  rw [Measure.bind_apply hE K.aemeasurable,Measure.add_apply,
    Measure.smul_apply,Measure.smul_apply,Measure.bind_apply hE R.aemeasurable]
  have hrow (y : Y) : K y E = ENNReal.ofReal (1-r)*ξ.toMeasure E + ENNReal.ofReal r*R y E := by
    rw [hmix y,Measure.add_apply,Measure.smul_apply,Measure.smul_apply]
    rfl
  simp_rw [hrow]
  simp only [smul_eq_mul]
  rw [lintegral_add_left measurable_const,lintegral_const_mul _ (R.measurable_coe hE)]
  simp

noncomputable def common (R : Kernel Y Y) (ξ : ProbabilityMeasure Y) (r : ℝ) : ℕ → Measure Y
  | 0 => 0
  | n+1 => ENNReal.ofReal (1-r) • ξ.toMeasure + ENNReal.ofReal r • (R ∘ₘ common R ξ r n)

instance common_finite (R : Kernel Y Y) [IsMarkovKernel R] (ξ : ProbabilityMeasure Y)
    (r : ℝ) (n : ℕ) : IsFiniteMeasure (common R ξ r n) := by
  induction n with
  | zero => exact inferInstanceAs (IsFiniteMeasure (0 : Measure Y))
  | succ n ih =>
    letI := ih
    change IsFiniteMeasure (ENNReal.ofReal (1-r) • ξ.toMeasure +
      ENNReal.ofReal r • (R ∘ₘ common R ξ r n))
    letI := Measure.smul_finite ξ.toMeasure (c := ENNReal.ofReal (1-r)) ENNReal.ofReal_ne_top
    letI := Measure.smul_finite (R ∘ₘ common R ξ r n) (c := ENNReal.ofReal r) ENNReal.ofReal_ne_top
    infer_instance

theorem common_le_orbit (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ : ProbabilityMeasure Y) {r : ℝ} (hmix : IsMixture R K ξ r) (n : ℕ) :
    common R ξ r n ≤ orbitLaw K μ n := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    rw [common,orbitLaw,comp_mixture R K ξ hmix]
    exact add_le_add le_rfl (smul_mono_measure _ (comp_mono R ih))

theorem common_le_invariant (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ π : ProbabilityMeasure Y) {r : ℝ} (hmix : IsMixture R K ξ r)
    (hπ : K ∘ₘ π.toMeasure = π.toMeasure) (n : ℕ) : common R ξ r n ≤ π.toMeasure := by
  induction n with
  | zero => exact bot_le
  | succ n ih =>
    rw [common,← hπ,comp_mixture R K ξ hmix]
    exact add_le_add le_rfl (smul_mono_measure _ (comp_mono R ih))

theorem common_mass (R : Kernel Y Y) [IsMarkovKernel R] (ξ : ProbabilityMeasure Y)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    common R ξ r n univ = ENNReal.ofReal (1-r^n) := by
  induction n with
  | zero => simp [common]
  | succ n ih =>
    have hR : (R ∘ₘ common R ξ r n) univ = common R ξ r n univ := by
      rw [Measure.bind_apply MeasurableSet.univ R.aemeasurable]
      simp
    have hpow : 0 ≤ 1-r^n := sub_nonneg.mpr (pow_le_one₀ hr hr1.le)
    simp only [common,Measure.add_apply,Measure.smul_apply,smul_eq_mul,measure_univ,mul_one]
    rw [hR,ih,← ENNReal.ofReal_mul hr,← ENNReal.ofReal_add
      (sub_nonneg.mpr hr1.le) (mul_nonneg hr hpow)]
    congr 1
    rw [pow_succ]
    ring

theorem orbit_tv_le_pow (R K : Kernel Y Y) [IsMarkovKernel R] [IsMarkovKernel K]
    (ξ μ π : ProbabilityMeasure Y) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hmix : IsMixture R K ξ r) (hπ : K ∘ₘ π.toMeasure = π.toMeasure) (n : ℕ) :
    eventTotalVariation (orbitLaw K μ n) π.toMeasure ≤ r^n := by
  have htv := eventTotalVariation_le_one_sub_commonMass
    (common_le_orbit R K ξ μ hmix n) (common_le_invariant R K ξ π hmix hπ n)
  have he : (common R ξ r n).real univ = 1-r^n := by
    rw [Measure.real,common_mass R ξ hr hr1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr (pow_le_one₀ hr hr1.le))]
  rw [he] at htv
  linarith

end PermanssonResearch.Probability.RegenerativeRenewal
