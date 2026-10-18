import PermanssonResearch.EconomicWitness.Geometry
import PermanssonLean.Regime.Persistence
import PermanssonResearch.MultipleLimit.FiniteExactGRRecovery
import PermanssonResearch.MultipleLimit.FiniteOccupationMeasureBridge

/-! Original Exact GR via the actual finite Markov residual strong law. -/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology
namespace PermanssonResearch.EconomicWitness
open PermanssonLean PermanssonLean.RegimeSpecification ActionTrace
open MultipleLimit MultipleLimit.FiniteCanonicalPath MultipleLimit.FiniteOccupationStrongLaw
open MultipleLimit.FiniteOccupationVector MultipleLimit.FiniteOccupationTelescoping
open MultipleLimit.FiniteCesaroAlgebra MultipleLimit.FiniteKernelRealBridge
open MultipleLimit.FiniteKernelInvariantUniqueness MultipleLimit.FiniteOccupationMeasureBridge
set_option autoImplicit false
attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable def stateTarget : ProbabilityMeasure Y :=
  ⟨(fairRow.map (fun x => ((),x))).measure, inferInstance⟩

theorem stateTarget_real (y : Y) : realPointMass stateTarget y = if y.2 = 2 then 0 else 1/2 := by
  rcases y with ⟨u,x⟩
  cases u
  fin_cases x <;>
    norm_num [realPointMass, stateTarget, Row.measure_singleton, Row.map, fairRow,
      Fin.sum_univ_three, Measure.real_def]

theorem realTransition_entry (y z : Y) :
    realTransition model.inducedKernel y z =
      if y.2 = 2 then (if z.2 = 2 then 1 else 0)
      else if z.2 = 2 then 0 else 1/2 := by
  unfold realTransition
  rw [induced_atom]
  split_ifs <;> norm_num

/-- Exact invariance gives persistence under EVERY admitted initial law,
using the already-proved canonical finite-state mixture identity. -/
theorem baseline_survival (μ : ProbabilityMeasure Y)
    (hμ : IsAdmissibleInitialLaw specification μ) :
    model.pathLaw μ.toMeasure (survivesForeverSet specification) = 1 := by
  have hm : μ.toMeasure region = 1 := hμ
  have hcomp : μ.toMeasure regionᶜ = 0 := by
    rw [prob_compl_eq_one_sub MeasurableSet.of_discrete, hm]
    simp
  have hz : μ.toMeasure {((),(2:World))} = 0 := by
    apply measure_mono_null _ hcomp
    intro y hy
    have heq : y = ((),(2:World)) := Set.mem_singleton_iff.mp hy
    subst y
    simp [region]
  have h0 : model.pathLaw (Measure.dirac ((),(0:World)))
      (survivesForeverSet specification) = 1 :=
    exactInvariant_survivalForever model specification original_exact_invariance (by simp [specification, region])
  have h1 : model.pathLaw (Measure.dirac ((),(1:World)))
      (survivesForeverSet specification) = 1 :=
    exactInvariant_survivalForever model specification original_exact_invariance (by simp [specification, region])
  have hmix := canonicalPathLaw_event_initial_mixture model.inducedKernel μ
    (survivesForeverSet specification) (measurableSet_survivesForeverSet specification)
  simp_rw [← typed_pathLaw_eq_canonical] at hmix
  rw [hmix]
  have hsum : μ.toMeasure {((),(0:World))} + μ.toMeasure {((),(1:World))} = 1 := by
    rw [region_eq_pair] at hm
    have hp : ({((),(0:World)),((),(1:World))} : Set Y) =
      (↑({((),(0:World)),((),(1:World))} : Finset Y) : Set Y) := by simp
    rw [hp, ← sum_measure_singleton] at hm
    simpa using hm
  simpa only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_unique,
    h0, h1, hz, mul_one, zero_mul, add_zero] using hsum

theorem baseline_paths_functioning (μ : ProbabilityMeasure Y)
    (hμ : IsAdmissibleInitialLaw specification μ) :
    ∀ᵐ w ∂model.pathLaw μ.toMeasure, ∀ t, (w t).2 ≠ 2 := by
  have hh : ∀ᵐ w ∂model.pathLaw μ.toMeasure, w ∈ survivesForeverSet specification := by
    apply (ae_mem_iff_measure_eq (measurableSet_survivesForeverSet specification).nullMeasurableSet).2
    simpa using baseline_survival μ hμ
  exact hh

theorem empirical_collapse_zero (w : ℕ → Y) (hB : ∀ t, (w t).2 ≠ 2) (n : ℕ) :
    empiricalVector w n ((),2) = 0 := by
  unfold empiricalVector
  have hi (t : ℕ) : indicatorAt w ((),(2:World)) t = 0 := by
    have hn : w t ≠ ((),(2:World)) := fun hh => hB t (congrArg Prod.snd hh)
    simp [indicatorAt, hn]
  simp_rw [hi]
  simp

theorem empirical_push_functioning (w : ℕ → Y) (hB : ∀ t, (w t).2 ≠ 2)
    (n : ℕ) (z : Y) (hz : z.2 ≠ 2) :
    pushVector (realTransition model.inducedKernel) (empiricalVector w n) z = 1/2 := by
  have ht := empiricalVector_total w n
  have hc := empirical_collapse_zero w hB n
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_unique] at ht
  unfold pushVector
  simp only [Fintype.sum_prod_type, Fin.sum_univ_three, Fintype.sum_unique,
    realTransition_entry, hz, if_false, show (0 : World) ≠ 2 by decide,
    show (1 : World) ≠ 2 by decide, if_pos, hc]
  linarith

/-- For functioning trajectories, the strong-law stationarity residual forces
both resource frequencies to one half and collapse frequency to zero. -/
theorem empirical_vector_target (w : ℕ → Y) (hB : ∀ t, (w t).2 ≠ 2)
    (hres : ∀ z, Tendsto (fun n => pushVector (realTransition model.inducedKernel)
      (empiricalVector w n) z - empiricalVector w n z) atTop (𝓝 0)) :
    Tendsto (fun n => empiricalVector w n) atTop (𝓝 (realPointMass stateTarget)) := by
  apply tendsto_pi_nhds.mpr
  intro z
  rw [stateTarget_real]
  by_cases hz : z.2 = 2
  · rw [if_pos hz]
    have heq : z = ((),(2:World)) := by
      apply Prod.ext
      · exact Subsingleton.elim _ _
      · exact hz
    subst z
    simpa only [empirical_collapse_zero w hB] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
  · rw [if_neg hz]
    have hr := hres z
    simp_rw [empirical_push_functioning w hB _ z hz] at hr
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1/2 : ℝ)) atTop (𝓝 (1/2 : ℝ))).sub hr
    convert hh using 1 <;> simp

theorem descriptor_occupation_target (w : ℕ → Y)
    (hv : Tendsto (fun n => empiricalVector w n) atTop (𝓝 (realPointMass stateTarget))) :
    Tendsto (fun n => empiricalOccupation specification w (n+1) (Nat.succ_pos n))
      atTop (𝓝 target) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have hc (y : Y) := (tendsto_pi_nhds.mp hv) y
  have hs := tendsto_finsetSum (Finset.univ : Finset Y)
    (fun y _ => (hc y).mul_const (f y.2))
  have hemp (n : ℕ) :
      (∫ x, f x ∂(empiricalOccupation specification w (n+1) (Nat.succ_pos n)).toMeasure) =
        ∑ y : Y, empiricalVector w n y * f y.2 := by
    rw [FiniteExactGRRecovery.original_empirical_eq_physical_map]
    change (∫ x, f x ∂Measure.map Prod.snd
      (FiniteStateOccupation.empiricalOccupation w (n+1) (Nat.succ_pos n)).toMeasure) = _
    rw [integral_map_of_stronglyMeasurable measurable_snd (.of_discrete),
      integral_fintype (Integrable.of_finite)]
    simp only [empiricalOccupation_singleton_real, smul_eq_mul]
  have htarget : (∫ x, f x ∂target.toMeasure) =
      ∑ y : Y, realPointMass stateTarget y * f y.2 := by
    calc
      _ = fairRow.expect (fun x => f x) := (Row.expect_eq_integral _ _).symm
      _ = (fairRow.map (fun x => ((),x))).expect (fun y => f y.2) :=
        (Row.expect_map fairRow (fun x => ((),x)) (fun y : Y => f y.2)).symm
      _ = ∫ y, f y.2 ∂stateTarget.toMeasure := Row.expect_eq_integral _ _
      _ = _ := by
        rw [integral_fintype (Integrable.of_finite)]
        simp [realPointMass, Measure.real_def, smul_eq_mul]
  simpa only [hemp, htarget] using hs

/-- The original almost-sure weak occupation gate for every basin-supported
initial probability law, proved via the actual finite Markov strong law. -/
theorem original_limiting_occupation (μ : ProbabilityMeasure Y)
    (hμ : IsAdmissibleInitialLaw specification μ) :
    IsLimitingOccupationLaw model specification μ := by
  have hr := canonical_empirical_residual_ae_zero model.inducedKernel μ
  rw [← typed_pathLaw_eq_canonical model μ.toMeasure] at hr
  unfold IsLimitingOccupationLaw
  change ∀ᵐ w ∂model.pathLaw μ.toMeasure,
    Tendsto (fun n => empiricalOccupation specification w (n+1) (Nat.succ_pos n)) atTop (𝓝 target)
  filter_upwards [baseline_paths_functioning μ hμ, hr] with w hB hres
  exact descriptor_occupation_target w (empirical_vector_target w hB hres)

theorem original_exactGR : IsExactGeneratedRegime model specification reference :=
  ⟨canonicalProcessWellPosed model, original_assumption41, original_exact_invariance,
    original_limiting_occupation⟩

theorem original_confirmatoryGR : IsConfirmatoryGeneratedRegime model specification reference :=
  ⟨original_exactGR, original_descriptor_nondegenerate⟩

end PermanssonResearch.EconomicWitness

