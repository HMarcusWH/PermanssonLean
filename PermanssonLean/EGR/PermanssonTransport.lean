import PermanssonLean.EGR.RegimeEmbedding
import PermanssonLean.Regime.Permansson
import PermanssonLean.Regime.UniformPermansson

open MeasureTheory ProbabilityTheory Set

namespace PermanssonLean

universe uX uA uH uZ

/-- Paper-I date/state policy intervention rule ρ_t^J(x).  Feasibility and
application-specific admissibility are frozen upstream; the measurable rule is
the object transported into the canonical action-selection intervention. -/
structure PaperIPolicyIntervention
    (X : Type uX) (A : Type uA)
    [MeasurableSpace X] [MeasurableSpace A] where
  rule : ℕ × X → A
  rule_measurable : Measurable rule

namespace PaperIPolicyIntervention

variable {X : Type uX} {A : Type uA} {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]

/-- State-indexed realization of ρ_t^J(x) on S_E × X. -/
def transportedActionMap
    (J : PaperIPolicyIntervention X A) :
    JointState (PaperIStrategicState A) X → A :=
  fun y => J.rule (y.1.1, y.2)

theorem transportedActionMap_measurable
    (J : PaperIPolicyIntervention X A) :
    Measurable J.transportedActionMap := by
  exact J.rule_measurable.comp
    ((measurable_fst.comp measurable_fst).prodMk measurable_snd)

/-- Canonical single-component family used to transport one Paper-I policy
protocol.  The family-level admissibility proof here records formal membership;
substantive feasibility is part of the Paper-I protocol certificate upstream. -/
def transportedFamily
    (M : PaperISelectedModel X A) :
    InterventionFamily M.embeddedModel Unit where
  targetOf _ := .actionSelection
  admissible _ _ := True

/-- Action-selection replacement α^J(da | (t,ā),x)=δ_{ρ_t^J(x)}(da). -/
noncomputable def transportedReplacement
    (J : PaperIPolicyIntervention X A) :
    InterventionReplacement
      (PaperIStrategicState A) X A .actionSelection where
  kernel := Kernel.deterministic
    J.transportedActionMap
    J.transportedActionMap_measurable
  isMarkov := by infer_instance

/-- Bundled admissible strategic intervention corresponding to the Paper-I
policy intervention. -/
noncomputable def transportedIntervention
    (M : PaperISelectedModel X A)
    (J : PaperIPolicyIntervention X A) :
    AdmissibleStrategicIntervention (transportedFamily M) where
  intervention := {
    component := ()
    replacement := J.transportedReplacement
  }
  accepted := trivial
  strategic := by simp [transportedFamily, TypedIntervention.IsStrategic]

@[simp]
theorem transportedIntervention_world_eq
    (M : PaperISelectedModel X A)
    (J : PaperIPolicyIntervention X A) :
    (J.transportedIntervention M).intervention.apply.world =
      M.embeddedModel.world :=
  (J.transportedIntervention M).world_eq

@[simp]
theorem transportedIntervention_update_eq
    (M : PaperISelectedModel X A)
    (J : PaperIPolicyIntervention X A) :
    (J.transportedIntervention M).intervention.apply.generator.update =
      M.embeddedModel.generator.update := by
  rfl

@[simp]
theorem transportedIntervention_action
    (M : PaperISelectedModel X A)
    (J : PaperIPolicyIntervention X A) :
    (J.transportedIntervention M).intervention.apply.generator.action =
      Kernel.deterministic
        J.transportedActionMap
        J.transportedActionMap_measurable := by
  rfl

/-- Paper-I counterfactual world-path law represented by the canonical
clock-state action-selection intervention and then decoded by world
projection. -/
noncomputable def counterfactualPathProbability
    (M : PaperISelectedModel X A)
    (J : PaperIPolicyIntervention X A)
    (x : X) :
    ProbabilityMeasure (ℕ → X) :=
  (RegimeSpecification.pathProbability
    (J.transportedIntervention M).intervention.apply
    (diracProba (M.initialEmbedding x))).map
      (PaperISelectedModel.worldPathProjection
        (X := X) (S := PaperIStrategicState A))

end PaperIPolicyIntervention

/-- Frozen Paper-I comparison set B₁.  Distinct states are sufficient for the
point-initialized path-law nontriviality required after embedding. -/
structure PaperIComparisonSet
    {X : Type uX} {H : Type uH}
    [MeasurableSpace X] [MeasurableSpace H]
    (spec : RegimeSpecification X H) where
  states : Set X
  states_measurable : MeasurableSet states
  states_subset_basin : states ⊆ spec.basin
  two_states :
    ∃ x₁ ∈ states, ∃ x₂ ∈ states, x₁ ≠ x₂

namespace PaperIComparisonSet

variable {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
variable [MeasurableSingletonClass A]
variable [MeasurableSpace.SeparatesPoints
  (JointState (PaperIStrategicState A) X)]

/-- Transport B₁ to B~₁=ι₀(B₁). -/
noncomputable def embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (B₁ : PaperIComparisonSet spec) :
    RegimeSpecification.ConstitutiveComparisonSet
      M.embeddedModel (M.embeddedSpec (A := A) spec) where
  states :=
    {M.initialStrategicState (A := A)} ×ˢ B₁.states
  states_measurable :=
    (measurableSet_singleton
      (M.initialStrategicState (A := A))).prod B₁.states_measurable
  states_subset_basin := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact ⟨hs, B₁.states_subset_basin hx⟩
  pathLawNontrivial := by
    rcases B₁.two_states with ⟨x₁, hx₁, x₂, hx₂, hne⟩
    let y₁ : JointState (PaperIStrategicState A) X :=
      (M.initialStrategicState (A := A), x₁)
    let y₂ : JointState (PaperIStrategicState A) X :=
      (M.initialStrategicState (A := A), x₂)
    have hyne : y₁ ≠ y₂ := by
      intro hp
      exact hne (congrArg Prod.snd hp)
    have hpath :
        M.embeddedModel.pathLaw (Measure.dirac y₁) ≠
          M.embeddedModel.pathLaw (Measure.dirac y₂) := by
      intro hpaths
      have hpref := congrArg
        (fun μ : Measure
          (ℕ → JointState (PaperIStrategicState A) X) =>
          μ.map (Preorder.frestrictLe 0)) hpaths
      rw [
        StrategicWorldModel.pathLaw_prefix_zero
          M.embeddedModel (Measure.dirac y₁),
        StrategicWorldModel.pathLaw_prefix_zero
          M.embeddedModel (Measure.dirac y₂)
      ] at hpref
      let e := MeasurableEquiv.piUnique
        (fun _ : ↥(Finset.Iic (0 : ℕ)) =>
          JointState (PaperIStrategicState A) X)
      have hpref' :
          (Measure.dirac y₁).map e.symm =
            (Measure.dirac y₂).map e.symm := by
        simpa [e] using hpref
      have hdirac : Measure.dirac y₁ = Measure.dirac y₂ :=
        e.symm.measurableEmbedding.map_injective hpref'
      exact hyne (MeasureTheory.dirac_eq_dirac_iff.mp hdirac)
    exact ⟨y₁, by exact ⟨rfl, hx₁⟩,
      y₂, by exact ⟨rfl, hx₂⟩, hpath⟩

end PaperIComparisonSet

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA} {H : Type uH} {Z : Type uZ}
variable [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]
variable [TopologicalSpace X] [TopologicalSpace A]
variable [MeasurableSingletonClass A]
variable [MeasurableSpace.SeparatesPoints
  (JointState (PaperIStrategicState A) X)]

/-- Transport a Paper-I world-path property to embedded state paths by world
projection. -/
noncomputable def transportProperty
    (ψI : RegimePropertyMap X Z) :
    RegimePropertyMap
      (JointState (PaperIStrategicState A) X) Z :=
  fun μ =>
    ψI (μ.map
      (worldPathProjection
        (X := X) (S := PaperIStrategicState A)))

/-- Baseline Paper-I property value at a point initialization. -/
noncomputable def paperIBaselinePropertyValue
    (M : PaperISelectedModel X A)
    (ψI : RegimePropertyMap X Z)
    (x : X) : Z :=
  ψI (M.pathProbability (diracProba x))

/-- Paper-I intervention property value at a point initialization. -/
noncomputable def paperIIntervenedPropertyValue
    (M : PaperISelectedModel X A)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (x : X) : Z :=
  ψI (J.counterfactualPathProbability M x)

theorem transported_baselinePropertyValue_eq
    (M : PaperISelectedModel X A)
    (ψI : RegimePropertyMap X Z)
    (x : X) :
    RegimeSpecification.baselinePropertyValue
        (M.transportProperty ψI) M.embeddedModel
        (M.initialEmbedding x) =
      M.paperIBaselinePropertyValue ψI x := by
  unfold RegimeSpecification.baselinePropertyValue
    transportProperty paperIBaselinePropertyValue
  apply congrArg ψI
  apply ProbabilityMeasure.toMeasure_injective
  change
    (M.embeddedModel.pathLaw
      (diracProba (M.initialEmbedding x)).toMeasure).map
        (worldPathProjection
          (X := X) (S := PaperIStrategicState A)) =
      M.pathLaw (diracProba x).toMeasure
  simpa [PaperISelectedModel.worldMarginal] using
    M.embedded_worldPathLaw_eq_paperI
      (diracProba (M.initialEmbedding x))

theorem transported_intervenedPropertyValue_eq
    (M : PaperISelectedModel X A)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (x : X) :
    RegimeSpecification.intervenedPropertyValue
        (M.transportProperty ψI)
        (J.transportedIntervention M).intervention
        (M.initialEmbedding x) =
      M.paperIIntervenedPropertyValue ψI J x := by
  rfl

/-- Paper-I pointwise constitutive protocol. -/
def IsPaperIConstitutive
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  ∀ x ∈ B₁.states,
    M.paperIBaselinePropertyValue ψI x ≠
      M.paperIIntervenedPropertyValue ψI J x

/-- Transported pointwise constitution is exactly the Paper-I protocol. -/
theorem paperIConstitutive_iff_embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    IsPaperIConstitutive M spec ψI J B₁ ↔
      RegimeSpecification.IsStrategicallyConstitutive
        M.embeddedModel
        (M.embeddedSpec (A := A) spec)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportProperty ψI)
        (B₁.embedded M spec)
        (J.transportedIntervention M) := by
  constructor
  · intro h y hy
    rcases hy.1 with rfl
    exact by
      simpa [
        M.transported_baselinePropertyValue_eq ψI y.2,
        M.transported_intervenedPropertyValue_eq ψI J y.2
      ] using h y.2 hy.2
  · intro h x hx
    have hy :
        (M.initialEmbedding x) ∈ (B₁.embedded M spec).states :=
      ⟨rfl, hx⟩
    have hh := h (M.initialEmbedding x) hy
    simpa [
      M.transported_baselinePropertyValue_eq ψI x,
      M.transported_intervenedPropertyValue_eq ψI J x
    ] using hh

/-- Paper-I Permansson status relative to one transported policy protocol. -/
def IsPaperIPermanssonRegimeRelative
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  IsPaperIEGR M spec m ∧
    IsPaperIConstitutive M spec ψI J B₁

/-- Theorem 6.2, pointwise world-path core. -/
theorem paperIPermansson_iff_embeddedRelativePR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    IsPaperIPermanssonRegimeRelative M spec m ψI J B₁ ↔
      RegimeSpecification.IsGeneralizedPermanssonRegimeRelative
        M.embeddedModel
        (M.embeddedSpec (A := A) spec)
        (M.embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportProperty ψI)
        (B₁.embedded M spec)
        (J.transportedIntervention M) := by
  unfold IsPaperIPermanssonRegimeRelative
    RegimeSpecification.IsGeneralizedPermanssonRegimeRelative
  rw [M.paperIEGR_iff_embeddedExactGR spec m,
      M.paperIConstitutive_iff_embedded spec ψI J B₁]

section Metric

variable [MetricSpace Z]

/-- Paper-I pointwise constitutive effect. -/
noncomputable def paperIConstitutiveEffect
    (M : PaperISelectedModel X A)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (x : X) : ℝ :=
  dist
    (M.paperIBaselinePropertyValue ψI x)
    (M.paperIIntervenedPropertyValue ψI J x)

/-- Paper-I uniform constitutive margin on B₁. -/
noncomputable def paperIConstitutiveMargin
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : ℝ :=
  sInf (M.paperIConstitutiveEffect ψI J '' B₁.states)

def IsPaperIUniformlyConstitutive
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  0 < M.paperIConstitutiveMargin spec ψI J B₁

theorem transported_constitutiveEffect_eq
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec)
    (x : X) :
    M.paperIConstitutiveEffect ψI J x =
      RegimeSpecification.constitutiveEffect
        M.embeddedModel
        (M.transportProperty ψI)
        (J.transportedIntervention M)
        (M.initialEmbedding x) := by
  unfold paperIConstitutiveEffect
    RegimeSpecification.constitutiveEffect
  rw [M.transported_baselinePropertyValue_eq ψI x,
      M.transported_intervenedPropertyValue_eq ψI J x]

theorem paperIConstitutiveMargin_eq_embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    M.paperIConstitutiveMargin spec ψI J B₁ =
      RegimeSpecification.constitutiveMargin
        M.embeddedModel
        (M.embeddedSpec (A := A) spec)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportProperty ψI)
        (B₁.embedded M spec)
        (J.transportedIntervention M) := by
  unfold paperIConstitutiveMargin RegimeSpecification.constitutiveMargin
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨M.initialEmbedding x, ⟨rfl, hx⟩, ?_⟩
    exact M.transported_constitutiveEffect_eq spec ψI J B₁ x
  · rintro ⟨y, hy, rfl⟩
    rcases hy.1 with rfl
    refine ⟨y.2, hy.2, ?_⟩
    exact (M.transported_constitutiveEffect_eq
      spec ψI J B₁ y.2).symm

theorem paperIUniformlyConstitutive_iff_embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    IsPaperIUniformlyConstitutive M spec ψI J B₁ ↔
      RegimeSpecification.IsUniformlyStrategicallyConstitutive
        M.embeddedModel
        (M.embeddedSpec (A := A) spec)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportProperty ψI)
        (B₁.embedded M spec)
        (J.transportedIntervention M) := by
  unfold IsPaperIUniformlyConstitutive
  rw [RegimeSpecification.uniformlyConstitutive_iff_margin_pos,
      M.paperIConstitutiveMargin_eq_embedded spec ψI J B₁]

def IsPaperIUniformPermanssonRegimeRelative
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) : Prop :=
  IsPaperIEGR M spec m ∧
    IsPaperIUniformlyConstitutive M spec ψI J B₁

theorem paperIUniformPermansson_iff_embeddedRelativePR
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (m : Measure X)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    IsPaperIUniformPermanssonRegimeRelative
        M spec m ψI J B₁ ↔
      RegimeSpecification.IsUniformGeneralizedPermanssonRegimeRelative
        M.embeddedModel
        (M.embeddedSpec (A := A) spec)
        (M.embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (M.transportProperty ψI)
        (B₁.embedded M spec)
        (J.transportedIntervention M) := by
  unfold IsPaperIUniformPermanssonRegimeRelative
    RegimeSpecification.IsUniformGeneralizedPermanssonRegimeRelative
  rw [M.paperIEGR_iff_embeddedExactGR spec m,
      M.paperIUniformlyConstitutive_iff_embedded spec ψI J B₁]

end Metric

end PaperISelectedModel

end PermanssonLean
