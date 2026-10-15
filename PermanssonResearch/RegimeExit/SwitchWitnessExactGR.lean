import PermanssonResearch.RegimeExit.SwitchWitnessGeometry
import PermanssonLean.Regime.GeneratedRegime
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Tactic

/-!
# C-Exit B — independently certified source and target Exact GRs

Both source and target are complete ORIGINAL IsExactGeneratedRegime
objects, with distinct invariant regions and disjoint basins.
The shared Boolean observed outcome is nonconstant on each region
but labels every recurrent state true, hence has a canonical
almost-sure weak limiting occupation law from all initial measures.
No empirical calibration or exogenous matrix assumption is involved.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace PermanssonResearch.RegimeExit.SwitchWitnessExactGR

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.RegimeExit.SwitchWitnessModels
open PermanssonResearch.RegimeExit.SwitchWitnessGeometry
open PermanssonResearch.MultipleLimit
open PermanssonResearch.MultipleLimit.FiniteCanonicalPath
open PermanssonResearch.MultipleLimit.FiniteEventuallyObserved

attribute [local instance] PermanssonLean.StrategicWorldModel.inducedKernel_isMarkov

noncomputable section

/-- Baseline regime: B={0,1,4}, B0={0,1}. Observed h is false
at 0 and 1 but true at the unique reachable absorbing source 4. -/
def sourceObservedSpec : RegimeSpecification Y Bool where
  region := sourceSpec.region
  region_measurable := sourceSpec.region_measurable
  basin := sourceSpec.basin
  basin_measurable := sourceSpec.basin_measurable
  basin_subset_region := sourceSpec.basin_subset_region
  descriptor := observed
  descriptor_measurable := Measurable.of_discrete
  target := diracProba true
  convergenceMode := ConvergenceMode.almostSureWeak Y Bool

/-- Post-J destination regime: B'=B0'={2,3}; the observed law
converges to true because state 2 proceeds to absorbing state 3. -/
def targetObservedSpec : RegimeSpecification Y Bool where
  region := targetSpec.region
  region_measurable := targetSpec.region_measurable
  basin := targetSpec.basin
  basin_measurable := targetSpec.basin_measurable
  basin_subset_region := targetSpec.basin_subset_region
  descriptor := observed
  descriptor_measurable := Measurable.of_discrete
  target := diracProba true
  convergenceMode := ConvergenceMode.almostSureWeak Y Bool

def reference : Measure Y := Measure.count

theorem source_assumption41 :
    Assumption41 baselineModel sourceObservedSpec reference := by
  refine ⟨⟨decode (0 : Fin 5), by
    simp [sourceObservedSpec, sourceSpec, decode]⟩, ?_, ?_, ?_⟩
  · right
    have hmem : decode (0 : Fin 5) ∈ sourceObservedSpec.region := by
      simp [sourceObservedSpec, sourceSpec, decode]
    have hsingleton : (0 : ℝ≥0∞) <
        reference ({decode (0 : Fin 5)} : Set Y) := by
      simp [reference]
    exact lt_of_lt_of_le hsingleton (measure_mono
      (Set.singleton_subset_iff.mpr hmem))
  · refine ⟨decode (0 : Fin 5), by
      simp [sourceObservedSpec, sourceSpec, decode],
      decode (4 : Fin 5), by
      simp [sourceObservedSpec, sourceSpec, decode], ?_⟩
    change observed (decode (0 : Fin 5)) ≠ observed (decode (4 : Fin 5))
    decide
  · apply two_states_implies_basinPathLawNontrivial
      baselineModel sourceObservedSpec
    refine ⟨decode (0 : Fin 5), ?_, decode (1 : Fin 5), ?_, ?_⟩
    · simp [sourceObservedSpec, sourceSpec, decode]
    · simp [sourceObservedSpec, sourceSpec, decode]
    · decide

theorem target_assumption41 :
    Assumption41 fullModel targetObservedSpec reference := by
  refine ⟨⟨decode (2 : Fin 5), by
    simp [targetObservedSpec, targetSpec, decode]⟩, ?_, ?_, ?_⟩
  · right
    have hmem : decode (2 : Fin 5) ∈ targetObservedSpec.region := by
      simp [targetObservedSpec, targetSpec, decode]
    have hsingleton : (0 : ℝ≥0∞) <
        reference ({decode (2 : Fin 5)} : Set Y) := by
      simp [reference]
    exact lt_of_lt_of_le hsingleton (measure_mono
      (Set.singleton_subset_iff.mpr hmem))
  · refine ⟨decode (2 : Fin 5), by
      simp [targetObservedSpec, targetSpec, decode],
      decode (3 : Fin 5), by
      simp [targetObservedSpec, targetSpec, decode], ?_⟩
    change observed (decode (2 : Fin 5)) ≠ observed (decode (3 : Fin 5))
    decide
  · apply two_states_implies_basinPathLawNontrivial
      fullModel targetObservedSpec
    refine ⟨decode (2 : Fin 5), ?_, decode (3 : Fin 5), ?_, ?_⟩
    · simp [targetObservedSpec, targetSpec, decode]
    · simp [targetObservedSpec, targetSpec, decode]
    · decide

theorem source_observed_invariant :
    IsExactlyInvariant baselineModel sourceObservedSpec := by
  change IsExactlyInvariant baselineModel sourceSpec
  exact source_exactlyInvariant

theorem target_observed_invariant :
    IsExactlyInvariant fullModel targetObservedSpec := by
  change IsExactlyInvariant fullModel targetSpec
  exact target_exactlyInvariant

/-- The frozen original occupation process is an exact map of the
finite physical occupation at every positive horizon. -/
theorem source_empirical_eq (w : ℕ → Y) (T : ℕ) (hT : 0 < T) :
    empiricalOccupation sourceObservedSpec w T hT =
      observedEmpirical observed w T hT := by
  change empiricalOccupation sourceObservedSpec w T hT =
    (FiniteStateOccupation.empiricalOccupation w T hT).map
      sourceObservedSpec.descriptor
  exact FiniteExactGRRecovery.original_empirical_eq_physical_map
    sourceObservedSpec w T hT

theorem target_empirical_eq (w : ℕ → Y) (T : ℕ) (hT : 0 < T) :
    empiricalOccupation targetObservedSpec w T hT =
      observedEmpirical observed w T hT := by
  change empiricalOccupation targetObservedSpec w T hT =
    (FiniteStateOccupation.empiricalOccupation w T hT).map
      targetObservedSpec.descriptor
  exact FiniteExactGRRecovery.original_empirical_eq_physical_map
    targetObservedSpec w T hT

theorem source_observed_limit_from_any_law (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂baselineModel.pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        empiricalOccupation sourceObservedSpec w
          (n+1) (Nat.succ_pos n))
        atTop (𝓝 (diracProba true)) := by
  have h :=
    canonical_observed_occupation_ae_true
      baselineModel.inducedKernel observed
      baseline_recurrent_observed_true μ
  rw [← typed_pathLaw_eq_canonical baselineModel μ.toMeasure] at h
  filter_upwards [h] with w hw
  simpa only [source_empirical_eq] using hw

theorem target_observed_limit_from_any_law (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂fullModel.pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        empiricalOccupation targetObservedSpec w
          (n+1) (Nat.succ_pos n))
        atTop (𝓝 (diracProba true)) := by
  have h :=
    canonical_observed_occupation_ae_true
      fullModel.inducedKernel observed
      full_recurrent_observed_true μ
  rw [← typed_pathLaw_eq_canonical fullModel μ.toMeasure] at h
  filter_upwards [h] with w hw
  simpa only [target_empirical_eq] using hw

/-- FULL ORIGINAL Exact GR, all clauses, for the source. -/
theorem source_exactGR :
    IsExactGeneratedRegime baselineModel sourceObservedSpec reference := by
  refine ⟨canonicalProcessWellPosed baselineModel, source_assumption41,
    source_observed_invariant, ?_⟩
  intro μ _
  unfold IsLimitingOccupationLaw
  change ∀ᵐ w ∂baselineModel.pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        empiricalOccupation sourceObservedSpec w
          (n+1) (Nat.succ_pos n))
        atTop (𝓝 (diracProba true))
  exact source_observed_limit_from_any_law μ

/-- FULL ORIGINAL Exact GR for the strategically intervened target. -/
theorem target_exactGR :
    IsExactGeneratedRegime fullModel targetObservedSpec reference := by
  refine ⟨canonicalProcessWellPosed fullModel, target_assumption41,
    target_observed_invariant, ?_⟩
  intro μ _
  unfold IsLimitingOccupationLaw
  change ∀ᵐ w ∂fullModel.pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        empiricalOccupation targetObservedSpec w
          (n+1) (Nat.succ_pos n))
        atTop (𝓝 (diracProba true))
  exact target_observed_limit_from_any_law μ

end
end PermanssonResearch.RegimeExit.SwitchWitnessExactGR
