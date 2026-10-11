import PermanssonResearch.MultipleLimit.TypedEndpointInfiniteWeights
import PermanssonResearch.MultipleLimit.TypedRandomOccupation
import PermanssonResearch.MultipleLimit.MeasurableDestination
import Mathlib.Tactic

/-!
# Lane C1 — exact law of the random terminal absorber and Dirac measure

The true canonical path distribution from u has two genuinely different
absorbing outcomes. This connects the exact ever-hit probabilities to the
measurable terminal state, and then to the law of the measure-valued
almost-sure occupation limit. No deterministic barycenter is substituted.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PermanssonResearch
namespace MultipleLimit
namespace TypedTerminalEndpointLaw

open TypedStrategicWitness TypedEndpointEvents TypedEndpointInfiniteWeights
open TypedAbsorbingContinuation TypedAlmostSureAbsorption

noncomputable section

/-- On a probability-one set, the terminal-state random variable equals
a exactly when the canonical infinite path ever visits a. -/
theorem terminal_a_eq_ever_hit_ae (μ : ProbabilityMeasure Y) :
    {w : ℕ → Y | terminalDestination w = a} =ᵐ[model.pathLaw μ.toMeasure]
      (⋃ T : ℕ, TypedEndpointHitting.hitA T) := by
  filter_upwards [canonical_eventual_a_or_b μ,
    stays_after_absorbing_ae μ] with w hgood hstay
  have hcorrect : EventuallyAt w (terminalDestination w) :=
    terminalDestination_correct w
      (by simpa [TypedStrategicWitness.a, TypedStrategicWitness.b,
        absorbingA, absorbingB] using hgood)
  apply propext
  constructor
  · intro hterminal
    rw [hterminal] at hcorrect
    obtain ⟨N, hN⟩ := hcorrect
    exact Set.mem_iUnion.mpr ⟨N,
      (hitA_iff N w).mpr ⟨N, le_rfl, hN N le_rfl⟩⟩
  · intro hvisit
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hvisit
    obtain ⟨N, _, hN⟩ := (hitA_iff T w).mp hT
    have hmem : w N ∈ ({a,b} : Finset Y) := by simp [hN]
    have hfixed : EventuallyAt w a := by
      refine ⟨N, ?_⟩
      intro n hn
      exact (hstay N hmem n hn).trans hN
    exact (eventuallyAt_unique hfixed hcorrect).symm

theorem terminal_b_eq_ever_hit_ae (μ : ProbabilityMeasure Y) :
    {w : ℕ → Y | terminalDestination w = b} =ᵐ[model.pathLaw μ.toMeasure]
      (⋃ T : ℕ, TypedEndpointHitting.hitB T) := by
  filter_upwards [canonical_eventual_a_or_b μ,
    stays_after_absorbing_ae μ] with w hgood hstay
  have hcorrect : EventuallyAt w (terminalDestination w) :=
    terminalDestination_correct w
      (by simpa [TypedStrategicWitness.a, TypedStrategicWitness.b,
        absorbingA, absorbingB] using hgood)
  apply propext
  constructor
  · intro hterminal
    rw [hterminal] at hcorrect
    obtain ⟨N, hN⟩ := hcorrect
    exact Set.mem_iUnion.mpr ⟨N,
      (hitB_iff N w).mpr ⟨N, le_rfl, hN N le_rfl⟩⟩
  · intro hvisit
    obtain ⟨T, hT⟩ := Set.mem_iUnion.mp hvisit
    obtain ⟨N, _, hN⟩ := (hitB_iff T w).mp hT
    have hmem : w N ∈ ({a,b} : Finset Y) := by simp [hN]
    have hfixed : EventuallyAt w b := by
      refine ⟨N, ?_⟩
      intro n hn
      exact (hstay N hmem n hn).trans hN
    exact (eventuallyAt_unique hfixed hcorrect).symm

noncomputable def uPathProbability : ProbabilityMeasure (ℕ → Y) :=
  ⟨model.pathLaw (Measure.dirac u), inferInstance⟩

/-- Exact distribution of the actual canonical terminal state from u. -/
theorem terminal_a_weight_u :
    model.pathLaw (Measure.dirac u)
      {w : ℕ → Y | terminalDestination w = a} =
      ENNReal.ofReal (1/3 : ℝ) := by
  have h := terminal_a_eq_ever_hit_ae
    (⟨Measure.dirac u, inferInstance⟩ : ProbabilityMeasure Y)
  have heq := measure_congr h
  exact heq.trans ever_hit_a_u

theorem terminal_b_weight_u :
    model.pathLaw (Measure.dirac u)
      {w : ℕ → Y | terminalDestination w = b} =
      ENNReal.ofReal (2/3 : ℝ) := by
  have h := terminal_b_eq_ever_hit_ae
    (⟨Measure.dirac u, inferInstance⟩ : ProbabilityMeasure Y)
  have heq := measure_congr h
  exact heq.trans ever_hit_b_u

/-- The random Dirac measure at a receives probability 1/3. This is
a law on probability measures, not the average terminal state law. -/
theorem random_limit_a_weight_u
    (hA : MeasurableSet ({terminalLaw a} : Set (ProbabilityMeasure Y))) :
    (pathwiseRandomLimitLaw uPathProbability).toMeasure {terminalLaw a} =
      ENNReal.ofReal (1/3 : ℝ) := by
  rw [pathwiseRandomLimitLaw_apply uPathProbability _ hA]
  change model.pathLaw (Measure.dirac u)
    {w : ℕ → Y | terminalLaw (terminalDestination w) = terminalLaw a} = _
  have heq :
      {w : ℕ → Y | terminalLaw (terminalDestination w) = terminalLaw a} =
        {w : ℕ → Y | terminalDestination w = a} := by
    ext w
    exact terminalLaw_injective.eq_iff
  rw [heq]
  exact terminal_a_weight_u

theorem random_limit_b_weight_u
    (hB : MeasurableSet ({terminalLaw b} : Set (ProbabilityMeasure Y))) :
    (pathwiseRandomLimitLaw uPathProbability).toMeasure {terminalLaw b} =
      ENNReal.ofReal (2/3 : ℝ) := by
  rw [pathwiseRandomLimitLaw_apply uPathProbability _ hB]
  change model.pathLaw (Measure.dirac u)
    {w : ℕ → Y | terminalLaw (terminalDestination w) = terminalLaw b} = _
  have heq :
      {w : ℕ → Y | terminalLaw (terminalDestination w) = terminalLaw b} =
        {w : ℕ → Y | terminalDestination w = b} := by
    ext w
    exact terminalLaw_injective.eq_iff
  rw [heq]
  exact terminal_b_weight_u


/-- The same exact terminal weights hold from the deterministic entry state t. -/
theorem terminal_a_weight_t :
    model.pathLaw (Measure.dirac t)
      {w : ℕ → Y | terminalDestination w = a} =
      ENNReal.ofReal (1/3 : ℝ) := by
  have h := terminal_a_eq_ever_hit_ae
    (⟨Measure.dirac t, inferInstance⟩ : ProbabilityMeasure Y)
  exact (measure_congr h).trans ever_hit_a_t

theorem terminal_b_weight_t :
    model.pathLaw (Measure.dirac t)
      {w : ℕ → Y | terminalDestination w = b} =
      ENNReal.ofReal (2/3 : ℝ) := by
  have h := terminal_b_eq_ever_hit_ae
    (⟨Measure.dirac t, inferInstance⟩ : ProbabilityMeasure Y)
  exact (measure_congr h).trans ever_hit_b_t

end
end TypedTerminalEndpointLaw
end MultipleLimit
end PermanssonResearch
