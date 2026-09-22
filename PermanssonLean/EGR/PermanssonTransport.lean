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
  change
    (applyReplacement M.embeddedModel .actionSelection
      J.transportedReplacement).generator.update =
      M.embeddedModel.generator.update
  exact applyReplacement_actionSelection_update
    M.embeddedModel J.transportedReplacement

@[simp]
theorem transportedIntervention_action
    (M : PaperISelectedModel X A)
    (J : PaperIPolicyIntervention X A) :
    (J.transportedIntervention M).intervention.apply.generator.action =
      Kernel.deterministic
        J.transportedActionMap
        J.transportedActionMap_measurable := by
  change
    (applyReplacement M.embeddedModel .actionSelection
      J.transportedReplacement).generator.action =
      Kernel.deterministic
        J.transportedActionMap
        J.transportedActionMap_measurable
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
    (diracProba (PaperISelectedModel.initialEmbedding (X := X) (A := A) x))).map
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
      M.embeddedModel (PaperISelectedModel.embeddedSpec (A := A) spec) where
  states :=
    {PaperISelectedModel.initialStrategicState (A := A)} ×ˢ B₁.states
  states_measurable :=
    (measurableSet_singleton
      (PaperISelectedModel.initialStrategicState (A := A))).prod B₁.states_measurable
  states_subset_basin := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact ⟨hs, B₁.states_subset_basin hx⟩
  pathLawNontrivial := by
    rcases B₁.two_states with ⟨x₁, hx₁, x₂, hx₂, hne⟩
    let y₁ : JointState (PaperIStrategicState A) X :=
      (PaperISelectedModel.initialStrategicState (A := A), x₁)
    let y₂ : JointState (PaperIStrategicState A) X :=
      (PaperISelectedModel.initialStrategicState (A := A), x₂)
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
        (PaperISelectedModel.transportProperty (A := A) ψI) M.embeddedModel
        (PaperISelectedModel.initialEmbedding (X := X) (A := A) x) =
      M.paperIBaselinePropertyValue ψI x := by
  unfold RegimeSpecification.baselinePropertyValue
    transportProperty paperIBaselinePropertyValue
  apply congrArg ψI
  apply ProbabilityMeasure.toMeasure_injective
  change
    (M.embeddedModel.pathLaw
      (diracProba (PaperISelectedModel.initialEmbedding (X := X) (A := A) x)).toMeasure).map
        (worldPathProjection
          (X := X) (S := PaperIStrategicState A)) =
      M.pathLaw (diracProba x).toMeasure
  have hproj :=
    M.embedded_worldPathLaw_eq_paperI
      (diracProba (PaperISelectedModel.initialEmbedding
        (X := X) (A := A) x))
  have hwm :
      PaperISelectedModel.worldMarginal (A := A)
          (diracProba (PaperISelectedModel.initialEmbedding
            (X := X) (A := A) x)) =
        diracProba x := by
    apply ProbabilityMeasure.toMeasure_injective
    change
      (Measure.dirac
        (PaperISelectedModel.initialEmbedding (X := X) (A := A) x)).map
          Prod.snd =
        Measure.dirac x
    exact Measure.map_dirac' measurable_snd _
  rw [hwm] at hproj
  exact hproj

theorem transported_intervenedPropertyValue_eq
    (M : PaperISelectedModel X A)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (x : X) :
    RegimeSpecification.intervenedPropertyValue
        (PaperISelectedModel.transportProperty (A := A) ψI)
        (J.transportedIntervention M).intervention
        (PaperISelectedModel.initialEmbedding (X := X) (A := A) x) =
      M.paperIIntervenedPropertyValue ψI J x := by
  unfold RegimeSpecification.intervenedPropertyValue
    paperIIntervenedPropertyValue
    PaperIPolicyIntervention.counterfactualPathProbability
    PaperISelectedModel.transportProperty
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
        (PaperISelectedModel.embeddedSpec (A := A) spec)
        (PaperIPolicyIntervention.transportedFamily M)
        (PaperISelectedModel.transportProperty (A := A) ψI)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  constructor
  · intro h y hy
    rcases y with ⟨s, x⟩
    have hs :
        s = PaperISelectedModel.initialStrategicState (A := A) :=
      Set.mem_singleton_iff.mp hy.1
    subst s
    simpa [
      M.transported_baselinePropertyValue_eq ψI x,
      M.transported_intervenedPropertyValue_eq ψI J x
    ] using h x hy.2
  · intro h x hx
    have hy :
        (PaperISelectedModel.initialEmbedding (X := X) (A := A) x) ∈
          (PaperIComparisonSet.embedded M spec B₁).states :=
      ⟨Set.mem_singleton _, hx⟩
    have hh := h
      (PaperISelectedModel.initialEmbedding (X := X) (A := A) x) hy
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
        (PaperISelectedModel.embeddedSpec (A := A) spec)
        (PaperISelectedModel.embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (PaperISelectedModel.transportProperty (A := A) ψI)
        (PaperIComparisonSet.embedded M spec B₁)
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
        (PaperISelectedModel.transportProperty (A := A) ψI)
        (J.transportedIntervention M)
        (PaperISelectedModel.initialEmbedding (X := X) (A := A) x) := by
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
        (PaperISelectedModel.embeddedSpec (A := A) spec)
        (PaperIPolicyIntervention.transportedFamily M)
        (PaperISelectedModel.transportProperty (A := A) ψI)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  unfold paperIConstitutiveMargin RegimeSpecification.constitutiveMargin
  apply congrArg sInf
  ext r
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨PaperISelectedModel.initialEmbedding
      (X := X) (A := A) x, ⟨Set.mem_singleton _, hx⟩, ?_⟩
    exact M.transported_constitutiveEffect_eq spec ψI J B₁ x
  · rintro ⟨y, hy, rfl⟩
    rcases y with ⟨s, x⟩
    have hs :
        s = PaperISelectedModel.initialStrategicState (A := A) :=
      Set.mem_singleton_iff.mp hy.1
    subst s
    refine ⟨x, hy.2, ?_⟩
    exact (M.transported_constitutiveEffect_eq
      spec ψI J B₁ x).symm

theorem paperIUniformlyConstitutive_iff_embedded
    (M : PaperISelectedModel X A)
    (spec : RegimeSpecification X H)
    (ψI : RegimePropertyMap X Z)
    (J : PaperIPolicyIntervention X A)
    (B₁ : PaperIComparisonSet spec) :
    IsPaperIUniformlyConstitutive M spec ψI J B₁ ↔
      RegimeSpecification.IsUniformlyStrategicallyConstitutive
        M.embeddedModel
        (PaperISelectedModel.embeddedSpec (A := A) spec)
        (PaperIPolicyIntervention.transportedFamily M)
        (PaperISelectedModel.transportProperty (A := A) ψI)
        (PaperIComparisonSet.embedded M spec B₁)
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
        (PaperISelectedModel.embeddedSpec (A := A) spec)
        (PaperISelectedModel.embeddedReferenceMeasure (A := A) m)
        (PaperIPolicyIntervention.transportedFamily M)
        (PaperISelectedModel.transportProperty (A := A) ψI)
        (PaperIComparisonSet.embedded M spec B₁)
        (J.transportedIntervention M) := by
  unfold IsPaperIUniformPermanssonRegimeRelative
    RegimeSpecification.IsUniformGeneralizedPermanssonRegimeRelative
  rw [M.paperIEGR_iff_embeddedExactGR spec m,
      M.paperIUniformlyConstitutive_iff_embedded spec ψI J B₁]

end Metric

end PaperISelectedModel

end PermanssonLean
