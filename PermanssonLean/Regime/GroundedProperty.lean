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
def IsGroundedPropertyRelative
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (g : GroundedRelevanceMap spec G)
    (J : AdmissibleStrategicIntervention F) : Prop :=
  ∃ ψG : RegimePropertyMap G Z,
    (∀ μ : ProbabilityMeasure (JointState S X),
      IsAdmissibleInitialLaw spec μ →
        ψ (pathProbability M μ) =
          ψG (g.pushPath (pathProbability M μ))) ∧
    (∀ μ : ProbabilityMeasure (JointState S X),
      IsAdmissibleInitialLaw spec μ →
        ψ (pathProbability J.intervention.apply μ) =
          ψG (g.pushPath
            (pathProbability J.intervention.apply μ)))

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
    IsGroundedPropertyRelative M spec F ψ g J := by
  refine ⟨h.groundedProperty, ?_, ?_⟩
  · intro μ hμ
    exact h.factor (pathProbability M μ)
  · intro μ hμ
    exact h.factor (pathProbability J.intervention.apply μ)

/-- A point initialization inside the frozen basin is admissible. -/
theorem dirac_admissible_of_mem
    (spec : RegimeSpecification (JointState S X) H)
    (y : JointState S X)
    (hy : y ∈ spec.basin) :
    IsAdmissibleInitialLaw spec (diracProba y) := by
  unfold IsAdmissibleInitialLaw
  exact diracProba_toMeasure_apply_of_mem hy

/-- Grounded baseline property value at every comparison state, exposing
the frozen grounded functional that witnesses the protocol. -/
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
    ∃ ψG : RegimePropertyMap G Z,
      baselinePropertyValue ψ M y =
        ψG (g.pushPath (pathProbability M (diracProba y))) := by
  rcases hg with ⟨ψG, hbase, hinter⟩
  refine ⟨ψG, ?_⟩
  unfold baselinePropertyValue
  exact hbase (diracProba y)
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
    ∃ ψG : RegimePropertyMap G Z,
      intervenedPropertyValue ψ J.intervention y =
        ψG (g.pushPath
          (pathProbability J.intervention.apply (diracProba y))) := by
  rcases hg with ⟨ψG, hbase, hinter⟩
  refine ⟨ψG, ?_⟩
  unfold intervenedPropertyValue
  exact hinter (diracProba y)
    (dirac_admissible_of_mem spec y (B₁.states_subset_basin hy))

/-- Both pointwise values are represented by the same frozen ψ_G. -/
theorem grounded_propertyValues
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
    ∃ ψG : RegimePropertyMap G Z,
      baselinePropertyValue ψ M y =
        ψG (g.pushPath (pathProbability M (diracProba y))) ∧
      intervenedPropertyValue ψ J.intervention y =
        ψG (g.pushPath
          (pathProbability J.intervention.apply (diracProba y))) := by
  rcases hg with ⟨ψG, hbase, hinter⟩
  refine ⟨ψG, ?_, ?_⟩
  · unfold baselinePropertyValue
    exact hbase (diracProba y)
      (dirac_admissible_of_mem spec y (B₁.states_subset_basin hy))
  · unfold intervenedPropertyValue
    exact hinter (diracProba y)
      (dirac_admissible_of_mem spec y (B₁.states_subset_basin hy))

end RegimeSpecification

end PermanssonLean
