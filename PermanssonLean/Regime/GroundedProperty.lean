import PermanssonLean.Regime.Relevance
import PermanssonLean.Regime.Constitution

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uS uX uA uH uG uZ uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {G : Type uG} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H] [MeasurableSpace G]

namespace RegimeSpecification

/-- Source-faithful groundedness relative to one frozen constitutive protocol.

The equalities are required on admissible baseline and intervened path laws,
rather than on every probability measure on path space. -/
structure IsGroundedPropertyRelative
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (J : AdmissibleStrategicIntervention F) : Prop where
  groundedProperty : RegimePropertyMap G Z
  baseline_eq :
    ∀ μ : ProbabilityMeasure (JointState S X),
      IsAdmissibleInitialLaw spec μ →
        ψ (pathProbability M μ) =
          groundedProperty (g.pushPath (pathProbability M μ))
  intervention_eq :
    ∀ μ : ProbabilityMeasure (JointState S X),
      IsAdmissibleInitialLaw spec μ →
        ψ (pathProbability J.intervention.apply μ) =
          groundedProperty
            (g.pushPath (pathProbability J.intervention.apply μ))

/-- Strong global factorization through g.  This is a convenient sufficient
condition for protocol-relative groundedness, not the definition itself. -/
structure GloballyFactorsThroughRelevanceMap
    (spec : RegimeSpecification (JointState S X) H)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G) where
  groundedProperty : RegimePropertyMap G Z
  factor :
    ∀ μ : ProbabilityMeasure (ℕ → JointState S X),
      ψ μ = groundedProperty (g.pushPath μ)

theorem GloballyFactorsThroughRelevanceMap.relative
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (J : AdmissibleStrategicIntervention F)
    (h : GloballyFactorsThroughRelevanceMap spec ψ g) :
    IsGroundedPropertyRelative M spec F ψ g J where
  groundedProperty := h.groundedProperty
  baseline_eq := by
    intro μ hμ
    exact h.factor (pathProbability M μ)
  intervention_eq := by
    intro μ hμ
    exact h.factor (pathProbability J.intervention.apply μ)

/-- A point initialization inside the frozen basin is admissible. -/
theorem dirac_admissible_of_mem
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X)
    (hy : y ∈ spec.basin) :
    IsAdmissibleInitialLaw spec (diracProba y) := by
  unfold IsAdmissibleInitialLaw
  exact diracProba_toMeasure_apply_of_mem hy

/-- Grounded baseline property value at every comparison state. -/
theorem grounded_baselinePropertyValue
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (hg : IsGroundedPropertyRelative M spec F ψ g J)
    (y : JointState S X)
    (hy : y ∈ B₁.states) :
    baselinePropertyValue ψ M y =
      hg.groundedProperty
        (g.pushPath (pathProbability M (diracProba y))) := by
  unfold baselinePropertyValue
  exact hg.baseline_eq (diracProba y)
    (dirac_admissible_of_mem spec y (B₁.states_subset_basin hy))

/-- Grounded intervened property value at every comparison state. -/
theorem grounded_intervenedPropertyValue
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (hg : IsGroundedPropertyRelative M spec F ψ g J)
    (y : JointState S X)
    (hy : y ∈ B₁.states) :
    intervenedPropertyValue ψ J.intervention y =
      hg.groundedProperty
        (g.pushPath
          (pathProbability J.intervention.apply (diracProba y))) := by
  unfold intervenedPropertyValue
  exact hg.intervention_eq (diracProba y)
    (dirac_admissible_of_mem spec y (B₁.states_subset_basin hy))

end RegimeSpecification

end PermanssonLean
