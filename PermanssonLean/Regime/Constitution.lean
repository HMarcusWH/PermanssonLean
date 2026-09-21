import PermanssonLean.Regime.Property

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uS uX uA uH uZ uK

variable {S : Type uS} {X : Type uX} {A : Type uA}
variable {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace S] [MeasurableSpace X] [MeasurableSpace A]
variable [MeasurableSpace H]

namespace RegimeSpecification

/-- Frozen comparison set B₁ used by the constitutive test.

The paper requires B₁ to be Borel, contained in the declared basin B₀, and
baseline-nontrivial in the strong path-law sense.  We keep that certificate
explicit instead of trying to manufacture a measurable witness set from
Assumption 4.1.
-/
structure ConstitutiveComparisonSet
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H) where
  states : Set (JointState S X)
  states_measurable : MeasurableSet states
  states_subset_basin : states ⊆ spec.basin
  pathLawNontrivial :
    ∃ y₁ ∈ states, ∃ y₂ ∈ states,
      M.pathLaw (Measure.dirac y₁) ≠
        M.pathLaw (Measure.dirac y₂)

/-- Every constitutive comparison state lies in the regime region because
B₁ ⊆ B₀ ⊆ B. -/
theorem ConstitutiveComparisonSet.states_subset_region
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (B₁ : ConstitutiveComparisonSet M spec) :
    B₁.states ⊆ spec.region := by
  intro y hy
  exact spec.basin_subset_region (B₁.states_subset_basin hy)

/-- The comparison set is nonempty, witnessed by its baseline path-law
nontriviality certificate. -/
theorem ConstitutiveComparisonSet.states_nonempty
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    (B₁ : ConstitutiveComparisonSet M spec) :
    B₁.states.Nonempty := by
  rcases B₁.pathLawNontrivial with ⟨y₁, hy₁, y₂, hy₂, hne⟩
  exact ⟨y₁, hy₁⟩

/-- Equation (15): a frozen admissible strategic intervention is constitutive
for ψ on B₁ when it changes the declared regime property at every comparison
state.

The intervened model is diagnostic: it is not required to remain a GR or to
satisfy an equilibrium condition.
-/
def IsStrategicallyConstitutive
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F) : Prop :=
  ∀ y ∈ B₁.states,
    baselinePropertyValue ψ M y ≠
      intervenedPropertyValue ψ J.intervention y

theorem strategicallyConstitutive_at
    (M : StrategicWorldModel S X A)
    (spec : RegimeSpecification (JointState S X) H)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (ψ : RegimePropertyMap (JointState S X) Z)
    (B₁ : ConstitutiveComparisonSet M spec)
    (J : AdmissibleStrategicIntervention F)
    (h : IsStrategicallyConstitutive M spec F ψ B₁ J)
    {y : JointState S X}
    (hy : y ∈ B₁.states) :
    baselinePropertyValue ψ M y ≠
      intervenedPropertyValue ψ J.intervention y :=
  h y hy

/-- Any intervention eligible to witness strategic constitution is admissible
in the frozen intervention family. -/
theorem constitutiveIntervention_isAdmissible
    (M : StrategicWorldModel S X A)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (J : AdmissibleStrategicIntervention F) :
    J.intervention.IsAdmissible :=
  J.accepted

/-- Any intervention eligible to witness strategic constitution targets the
strategic generator rather than the world-transition kernel. -/
theorem constitutiveIntervention_isStrategic
    (M : StrategicWorldModel S X A)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (J : AdmissibleStrategicIntervention F) :
    J.intervention.IsStrategic :=
  J.strategic

/-- Hold-fixed theorem inherited from the typed intervention grammar:
a constitutive strategic intervention leaves P exactly equal to baseline. -/
theorem constitutiveIntervention_world_eq
    (M : StrategicWorldModel S X A)
    {Component : Type uK}
    (F : InterventionFamily M Component)
    (J : AdmissibleStrategicIntervention F) :
    J.intervention.apply.world = M.world :=
  J.world_eq

end RegimeSpecification

end PermanssonLean
