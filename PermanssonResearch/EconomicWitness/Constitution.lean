import PermanssonResearch.EconomicWitness.ExactRegime
import PermanssonResearch.EconomicWitness.ConstitutionCore

namespace PermanssonResearch.EconomicWitness
open PermanssonLean PermanssonLean.RegimeSpecification

/-- Full ORIGINAL grounded-confirmatory uniform PR classifier; no gate is replaced. -/
theorem original_grounded_confirmatory_uniformPR :
    IsGroundedConfirmatoryUniformPermanssonRegimeRelative model specification reference
      family survivalProperty grounding comparisonSet extractionIntervention :=
  ⟨original_confirmatoryGR, original_uniform_constitution, original_grounded_property⟩

end PermanssonResearch.EconomicWitness
