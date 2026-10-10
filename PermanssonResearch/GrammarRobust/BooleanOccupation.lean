import PermanssonResearch.GrammarRobust.BooleanBaseline
import PermanssonLean.Examples.PeriodicExactGR
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Tactic

/-!
# Lane B: honest almost-sure weak occupation convergence

For the *actual* baseline model the next state is the fixed point q0 after
one transition, regardless of the initial state. This module proves the
canonical path law equals the push-forward of that deterministic trajectory
map and proves convergence of the canonical empirical occupation measures.
The frozen convergence mode remains `almostSureWeak`, never `custom`.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology ProbabilityTheory ENNReal
namespace PermanssonResearch
namespace GrammarRobust
namespace BooleanBaseline

open PermanssonLean PermanssonLean.RegimeSpecification BooleanModel

noncomputable section

def orbit (y : Y) : ℕ → Y
  | 0 => y
  | _ + 1 => q0

@[simp] theorem orbit_zero (y : Y) : orbit y 0 = y := rfl
@[simp] theorem orbit_succ (y : Y) (n : ℕ) : orbit y (n + 1) = q0 := rfl

theorem sum_orbit (y : Y) (f : Y → ℝ) (n : ℕ) :
    ∑ i ∈ Finset.range (n + 1), f (orbit y i) =
      f y + (n : ℝ) * f q0 := by
  induction n with
  | zero =>
      simp [orbit]
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, orbit_succ]
      push_cast
      ring

theorem empiricalIntegral_eq
    (y : Y) (f : Y → ℝ) (n : ℕ) :
    ∫ z, f z ∂(empiricalOccupation spec (orbit y)
      (n + 1) (Nat.succ_pos n)) =
      (((n + 1 : ℕ) : ℝ)⁻¹) * (f y + (n : ℝ) * f q0) := by
  change
    ∫ z, f z ∂(empiricalOccupation PermanssonLean.PeriodicExactGR.spec
      (orbit y) (n + 1) (Nat.succ_pos n)) = _
  rw [PermanssonLean.PeriodicExactGR.integral_empiricalOccupation_eq_average,
    sum_orbit]

theorem integral_target (f : Y → ℝ) :
    ∫ z, f z ∂target = f q0 := by
  change ∫ z, f z ∂Measure.dirac q0 = f q0
  simp

theorem empiricalIntegral_tendsto (y : Y) (f : Y → ℝ) :
    Tendsto
      (fun n : ℕ => ∫ z, f z ∂(empiricalOccupation spec
        (orbit y) (n + 1) (Nat.succ_pos n)))
      atTop (𝓝 (∫ z, f z ∂target)) := by
  rw [integral_target]
  have hidx : Tendsto (fun n : ℕ => n + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hinv : Tendsto
      (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ)))
      atTop (𝓝 (0 : ℝ)) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hidx
  have hsmall : Tendsto
      (fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ)⁻¹) * (f y - f q0))
      atTop (𝓝 (0 : ℝ)) := by
    simpa [one_div] using
      (hinv.mul_const (f y - f q0))
  have hconst : Tendsto (fun _ : ℕ => f q0) atTop (𝓝 (f q0)) :=
    tendsto_const_nhds
  have hlimit := hconst.add hsmall
  have hresult : Tendsto
      (fun n : ℕ => f q0 + (((n + 1 : ℕ) : ℝ)⁻¹) * (f y - f q0))
      atTop (𝓝 (f q0)) := by simpa using hlimit
  apply hresult.congr'
  filter_upwards with n
  rw [empiricalIntegral_eq]
  have hn : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  push_cast
  field_simp [hn]
  ring

theorem empiricalOccupation_orbit_tendsto (y : Y) :
    Tendsto
      (fun n : ℕ => empiricalOccupation spec
        (orbit y) (n + 1) (Nat.succ_pos n))
      atTop (𝓝 target) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  simpa using empiricalIntegral_tendsto y (fun z => f z)

theorem measurable_orbit : Measurable orbit := by
  rw [measurable_pi_iff]
  intro n
  exact Measurable.of_discrete

theorem stationaryHistoryKernel_eq_deterministic (n : ℕ) :
    StrategicWorldModel.stationaryHistoryKernel baseline.inducedKernel n =
      Kernel.deterministic
        (fun _ : (i : Finset.Iic n) → Y => q0)
        (by fun_prop) := by
  ext h E hE
  rw [StrategicWorldModel.stationaryHistoryKernel, Kernel.comap_apply]
  rw [inducedKernel_dirac]
  rw [Kernel.deterministic_apply]

noncomputable def orbitLaw (μ : ProbabilityMeasure Y) : Measure (ℕ → Y) :=
  μ.toMeasure.map orbit

instance orbitLaw_isProbability (μ : ProbabilityMeasure Y) :
    IsProbabilityMeasure (orbitLaw μ) := by
  unfold orbitLaw
  infer_instance

theorem orbitLaw_initialPrefix (μ : ProbabilityMeasure Y) :
    (orbitLaw μ).map (Preorder.frestrictLe 0) =
      μ.toMeasure.map
        (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Y)).symm := by
  unfold orbitLaw
  rw [Measure.map_map (by fun_prop) measurable_orbit]
  apply Measure.map_congr
  filter_upwards [] with y
  funext i
  have hi : (i : ℕ) = 0 :=
    Nat.eq_zero_of_le_zero (Finset.mem_Iic.mp i.2)
  change orbit y (i : ℕ) = y
  rw [hi, orbit_zero]

theorem orbitLaw_hasTransitionPair (μ : ProbabilityMeasure Y) :
    StrategicWorldModel.HasTransitionPair
      (orbitLaw μ) baseline.inducedKernel := by
  intro n
  rw [stationaryHistoryKernel_eq_deterministic n]
  rw [Measure.compProd_deterministic]
  unfold orbitLaw
  rw [Measure.map_map (by fun_prop) measurable_orbit]
  rw [Measure.map_map (by fun_prop) measurable_orbit]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [] with y
  simp [Function.comp_apply, orbit_succ]

theorem pathLaw_eq_orbitLaw (μ : ProbabilityMeasure Y) :
    baseline.pathLaw μ.toMeasure = orbitLaw μ := by
  exact (StrategicWorldModel.pathLaw_existsUnique baseline μ.toMeasure).unique
    (StrategicWorldModel.pathLaw_spec baseline μ.toMeasure)
    ⟨inferInstance, orbitLaw_initialPrefix μ, orbitLaw_hasTransitionPair μ⟩

def orbitPaths : Set (ℕ → Y) := Set.range orbit

theorem orbitPaths_measurable : MeasurableSet orbitPaths :=
  (Set.finite_range orbit).measurableSet

theorem orbitLaw_ae_orbitPaths (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂orbitLaw μ, w ∈ orbitPaths := by
  unfold orbitLaw
  apply (ae_mem_iff_measure_eq orbitPaths_measurable.nullMeasurableSet).2
  rw [Measure.map_apply measurable_orbit orbitPaths_measurable]
  haveI : IsProbabilityMeasure (Measure.map orbit μ.toMeasure) := by infer_instance
  rw [measure_univ]
  apply le_antisymm prob_le_one
  rw [← measure_univ]
  apply measure_mono
  intro y _
  exact Set.mem_preimage.mpr ⟨y, rfl⟩

/-- The baseline satisfies the literal canonical almost-sure weak mode for
every initial law, hence in particular every law supported on the basin. -/
theorem limitingOccupation (μ : ProbabilityMeasure Y) :
    IsLimitingOccupationLaw baseline spec μ := by
  unfold IsLimitingOccupationLaw
  change ∀ᵐ w ∂baseline.pathLaw μ.toMeasure,
    Tendsto (fun n : ℕ => empiricalOccupation spec w (n + 1)
      (Nat.succ_pos n)) atTop (𝓝 target)
  rw [pathLaw_eq_orbitLaw]
  filter_upwards [orbitLaw_ae_orbitPaths μ] with w hw
  rcases hw with ⟨y, rfl⟩
  exact empiricalOccupation_orbit_tendsto y

/-- Real baseline Exact GR; no custom convergence predicate or assumed limit. -/
theorem exactGR :
    IsExactGeneratedRegime baseline spec referenceMeasure := by
  refine ⟨canonicalProcessWellPosed baseline, assumption41,
    exactlyInvariant, ?_⟩
  intro μ _
  exact limitingOccupation μ

end

end BooleanBaseline
end GrammarRobust
end PermanssonResearch
