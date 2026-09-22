import PermanssonLean.Regime.Property

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uY uH uG

variable {Y : Type uY} {H : Type uH} {G : Type uG}
variable [MeasurableSpace Y] [MeasurableSpace H] [MeasurableSpace G]

namespace RegimeSpecification

/-- Frozen regime-observation map for the grounded confirmatory subclass.

This encodes the Section-5.2 factorization requirements
`B = g⁻¹(B_G)` and `h = h_G ∘ g`.  The semantic core only needs a
measurable observation space; paper-facing wrappers can impose a
standard-Borel structure on `G`. -/
structure GroundedRelevanceMap
    (spec : RegimeSpecification Y H)
    (G : Type uG) [MeasurableSpace G] where
  observe : Y → G
  observe_measurable : Measurable observe
  regimeRegion : Set G
  regimeRegion_measurable : MeasurableSet regimeRegion
  region_preimage :
    spec.region = observe ⁻¹' regimeRegion
  descriptor : G → H
  descriptor_measurable : Measurable descriptor
  descriptor_factor :
    spec.descriptor = descriptor ∘ observe

namespace GroundedRelevanceMap

/-- Coordinatewise observation of a complete state path. -/
def pathMap
    {spec : RegimeSpecification Y H}
    (g : GroundedRelevanceMap spec G) :
    (ℕ → Y) → (ℕ → G) :=
  fun w n => g.observe (w n)

theorem pathMap_measurable
    {spec : RegimeSpecification Y H}
    (g : GroundedRelevanceMap spec G) :
    Measurable g.pathMap := by
  refine Measurable.of_eval fun n => ?_
  exact g.observe_measurable.comp (measurable_pi_apply n)

/-- Push a complete path probability law through the frozen relevance map. -/
noncomputable def pushPath
    {spec : RegimeSpecification Y H}
    (g : GroundedRelevanceMap spec G)
    (μ : ProbabilityMeasure (ℕ → Y)) :
    ProbabilityMeasure (ℕ → G) :=
  μ.map g.pathMap

theorem region_membership_iff
    {spec : RegimeSpecification Y H}
    (g : GroundedRelevanceMap spec G)
    (y : Y) :
    y ∈ spec.region ↔ g.observe y ∈ g.regimeRegion := by
  rw [g.region_preimage]
  rfl

theorem descriptor_eq
    {spec : RegimeSpecification Y H}
    (g : GroundedRelevanceMap spec G)
    (y : Y) :
    spec.descriptor y = g.descriptor (g.observe y) := by
  change spec.descriptor y = (g.descriptor ∘ g.observe) y
  rw [g.descriptor_factor]

theorem descriptor_path_eq
    {spec : RegimeSpecification Y H}
    (g : GroundedRelevanceMap spec G)
    (w : ℕ → Y)
    (t : ℕ) :
    spec.descriptor (w t) =
      g.descriptor (g.pathMap w t) := by
  exact g.descriptor_eq (w t)

end GroundedRelevanceMap

end RegimeSpecification

end PermanssonLean
