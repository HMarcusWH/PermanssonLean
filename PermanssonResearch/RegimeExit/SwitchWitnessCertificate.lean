import PermanssonResearch.RegimeExit.SwitchWitnessExactGR
import PermanssonResearch.RegimeExit.SwitchGrounded
import PermanssonResearch.RegimeExit.SwitchRetentionMass
import Mathlib.Tactic

/-!
# C-Exit B — genuine source/destination Exact-GR switch witness

The pair of Exact GRs is independently mechanically proved in
SwitchWitnessExactGR; the typed intervention is the original
action-selection replacement with literally fixed world P and U.

This file intentionally does NOT infer uniform routing, original PR
constitution, or random-entry occupation without separate theorems.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace PermanssonResearch.RegimeExit.SwitchWitnessCertificate

set_option autoImplicit false

open PermanssonLean PermanssonLean.RegimeSpecification
open PermanssonResearch.RegimeExit.SwitchWitnessModels
open PermanssonResearch.RegimeExit.SwitchWitnessGeometry
open PermanssonResearch.RegimeExit.SwitchWitnessExactGR
open PermanssonResearch.ReverseSolver.FiniteStrategicRealization
open PermanssonResearch.RegimeExit

/-- Frozen ORIGINAL two-state comparison basin, not a post hoc
selected successful sample path. Its nontriviality certificate is
inherited from the independently proved source Assumption 4.1. -/
def comparison :
    ConstitutiveComparisonSet baselineModel sourceObservedSpec where
  states := sourceObservedSpec.basin
  states_measurable := sourceObservedSpec.basin_measurable
  states_subset_basin := Set.Subset.rfl
  pathLawNontrivial := source_assumption41.2.2.2

/-- Fully typed source and target Exact GR data, with genuinely disjoint
regime regions. The target certificate applies to the actual J-modified
canonical model, not a separately postulated target matrix. -/
theorem certified_full_source_target :
    CertifiedSwitchData baselineModel sourceObservedSpec targetObservedSpec
      reference reference (researchActionFamily baselineMatrix)
      comparison fullIntervention := by
  refine ⟨source_exactGR, ?_, ?_⟩
  · change IsExactGeneratedRegime fullModel targetObservedSpec reference
    exact target_exactGR
  · change Disjoint sourceSpec.region targetSpec.region
    exact source_target_disjoint

end PermanssonResearch.RegimeExit.SwitchWitnessCertificate
