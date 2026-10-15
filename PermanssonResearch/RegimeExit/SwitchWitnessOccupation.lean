import PermanssonResearch.RegimeExit.SwitchWitnessCertificate
import PermanssonResearch.RegimeExit.SwitchRetentionMass
import Mathlib.Tactic

/-!
# C-Exit B — pathwise occupation on successful five-state strategic switches

For the concrete finite model, the target's observed occupation law
is already proved to converge from ALL initial probability laws under
the full intervened kernel. This permits an honest conditional-on-first-
exit a.s. statement without pretending to have solved general stopped-
time restart or arbitrary custom ConvergenceMode transport.
-/

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal Topology

namespace PermanssonResearch.RegimeExit.SwitchWitnessOccupation

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.RegimeExit
open PermanssonResearch.RegimeExit.SwitchWitnessModels
open PermanssonResearch.RegimeExit.SwitchWitnessExactGR
open PermanssonResearch.RegimeExit.SwitchWitnessCertificate
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization

/-- Actual full-intervention infinite trajectories obey the original
target specification's occupation-law convergence. Here, unusually,
the observation is constant at all recurrent states of the full model,
so the result holds from every initial law (stronger than necessary). -/
theorem actual_full_target_occupation_ae (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂fullIntervention.intervention.apply.pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        empiricalOccupation targetObservedSpec w
          (n+1) (Nat.succ_pos n))
        atTop (𝓝 (diracProba true)) := by
  change ∀ᵐ w ∂fullModel.pathLaw μ.toMeasure,
      Tendsto (fun n : ℕ =>
        empiricalOccupation targetObservedSpec w
          (n+1) (Nat.succ_pos n))
        atTop (𝓝 (diracProba true))
  exact target_observed_limit_from_any_law μ

/-- A nonvacuous ACTUAL model-specific example of a single complete
switched trajectory statement: entry, indefinite destination retention
and limiting target observed occupation, all after the same typed J.
This is deliberately not a generic Proposition 4.2f random-entry law. -/
theorem actual_successful_switch_occupation_ae
    (μ : ProbabilityMeasure Y) :
    ∀ᵐ w ∂fullIntervention.intervention.apply.pathLaw μ.toMeasure,
      w ∈ firstExitEverDestination sourceObservedSpec
          targetObservedSpec.basin →
        (∃ n : ℕ,
          w ∈ firstExitAtDestination sourceObservedSpec n
            targetObservedSpec.basin ∧
          ∀ t ≥ n+1, w t ∈ targetObservedSpec.region) ∧
        Tendsto (fun n : ℕ =>
          empiricalOccupation targetObservedSpec w
            (n+1) (Nat.succ_pos n))
          atTop (𝓝 (diracProba true)) := by
  have hstay :=
    switch_eventual_retention_ae baselineModel sourceObservedSpec
      targetObservedSpec reference reference
      (researchActionFamily baselineMatrix) comparison
      fullIntervention certified_full_source_target μ
  have hocc := actual_full_target_occupation_ae μ
  filter_upwards [hstay, hocc] with w hs ho hroute
  exact ⟨hs hroute, ho⟩

end PermanssonResearch.RegimeExit.SwitchWitnessOccupation
