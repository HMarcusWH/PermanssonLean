import PermanssonLean.EGR.Projection
import PermanssonLean.Regime.GeneratedRegime
import Mathlib.Topology.Constructions.SumProd

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology

namespace PermanssonLean

universe uX uA uH

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA} {H : Type uH}
variable [MeasurableSpace X] [MeasurableSpace A] [MeasurableSpace H]

/-- Transport the frozen Paper-I convergence predicate to enlarged state paths
by projecting those paths back to their world coordinate.  The occupation
process argument on the enlarged state is intentionally ignored: the source
Paper-I convergence mode is evaluated on the projected Paper-I empirical
occupation process. -/
noncomputable def embeddedConvergenceMode
    (spec : RegimeSpecification X H) :
    ConvergenceMode
      (JointState (PaperIStrategicState A) X) H where
  holds μ _ ν :=
    spec.convergenceMode.holds
      (μ.map
        (worldPathProjection
          (X := X) (S := PaperIStrategicState A)))
      (empiricalOccupation spec)
      ν

/-- Theorem-6.1 lifted regime specification:
B~ = S_E × B, B~₀ = {(0,⊥)} × B₀, h~((t,ā),x)=h̄(x). -/
noncomputable def embeddedSpec
    [MeasurableSingletonClass A]
    (spec : RegimeSpecification X H) :
    RegimeSpecification
      (JointState (PaperIStrategicState A) X) H where
  region := Set.univ ×ˢ spec.region
  region_measurable :=
    MeasurableSet.univ.prod spec.region_measurable
  basin := {initialStrategicState (A := A)} ×ˢ spec.basin
  basin_measurable := by
    have ht : MeasurableSet ({0} : Set ℕ) :=
      measurableSet_singleton 0
    have ha :
        MeasurableSet
          ({Sum.inl ()} : Set (PaperIActionRecord A)) :=
      measurableSet_singleton (Sum.inl ())
    have hs :
        MeasurableSet
          ({initialStrategicState (A := A)} :
            Set (PaperIStrategicState A)) := by
      simpa [initialStrategicState] using ht.prod ha
    exact hs.prod spec.basin_measurable
  basin_subset_region := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact ⟨Set.mem_univ s, spec.basin_subset_region hx⟩
  descriptor := fun y => spec.descriptor y.2
  descriptor_measurable :=
    spec.descriptor_measurable.comp measurable_snd
  target := spec.target
  convergenceMode := embeddedConvergenceMode (A := A) spec

/-- Lift the Paper-I reference measure through ι₀. -/
noncomputable def embeddedReferenceMeasure
    (m : Measure X) :
    Measure (JointState (PaperIStrategicState A) X) :=
  m.map (initialEmbedding (X := X) (A := A))

/-- Lift a Paper-I initial probability law through ι₀. -/
noncomputable def embeddedInitialLaw
    (μ : ProbabilityMeasure X) :
    ProbabilityMeasure
      (JointState (PaperIStrategicState A) X) :=
  μ.map (initialEmbedding (X := X) (A := A))

/-- World marginal of an enlarged initial probability law. -/
noncomputable def worldMarginal
    (μ : ProbabilityMeasure
      (JointState (PaperIStrategicState A) X)) :
    ProbabilityMeasure X :=
  μ.map Prod.snd

@[simp]
theorem embeddedSpec_region
    [MeasurableSingletonClass A]
    (spec : RegimeSpecification X H) :
    (embeddedSpec (A := A) spec).region =
      Set.univ ×ˢ spec.region :=
  rfl

@[simp]
theorem embeddedSpec_basin
    [MeasurableSingletonClass A]
    (spec : RegimeSpecification X H) :
    (embeddedSpec (A := A) spec).basin =
      {initialStrategicState (A := A)} ×ˢ spec.basin :=
  rfl

@[simp]
theorem embeddedSpec_descriptor
    [MeasurableSingletonClass A]
    (spec : RegimeSpecification X H)
    (y : JointState (PaperIStrategicState A) X) :
    (embeddedSpec (A := A) spec).descriptor y =
      spec.descriptor y.2 :=
  rfl

theorem embeddedInitialLaw_admissible_iff
    [MeasurableSingletonClass A]
    (spec : RegimeSpecification X H)
    (μ : ProbabilityMeasure X) :
    IsAdmissibleInitialLaw
        (embeddedSpec (A := A) spec)
        (embeddedInitialLaw (A := A) μ) ↔
      IsAdmissibleInitialLaw spec μ := by
  unfold IsAdmissibleInitialLaw embeddedInitialLaw
  rw [ProbabilityMeasure.toMeasure_map]
  rw [Measure.map_apply
    (initialEmbedding_measurable (X := X) (A := A))
    (embeddedSpec (A := A) spec).basin_measurable]
  change μ.toMeasure
      ((initialEmbedding (X := X) (A := A)) ⁻¹'
        ({initialStrategicState (A := A)} ×ˢ spec.basin)) = 1 ↔
    μ.toMeasure spec.basin = 1
  have hpre :
      (initialEmbedding (X := X) (A := A)) ⁻¹'
          ({initialStrategicState (A := A)} ×ˢ spec.basin) =
        spec.basin := by
    ext x
    simp [initialEmbedding, initialStrategicState]
  rw [hpre]

@[simp]
theorem worldMarginal_embeddedInitialLaw
    (μ : ProbabilityMeasure X) :
    worldMarginal (A := A) (embeddedInitialLaw (A := A) μ) = μ := by
  apply ProbabilityMeasure.toMeasure_injective
  change
    Measure.map Prod.snd
        (Measure.map
          (initialEmbedding (X := X) (A := A)) μ.toMeasure) =
      μ.toMeasure
  rw [Measure.map_map
    measurable_snd
    (initialEmbedding_measurable (X := X) (A := A))]
  simp [Function.comp_def, initialEmbedding]

theorem worldMarginal_admissible_of_embedded
    [MeasurableSingletonClass A]
    (spec : RegimeSpecification X H)
    (μ : ProbabilityMeasure
      (JointState (PaperIStrategicState A) X))
    (hμ :
      IsAdmissibleInitialLaw
        (embeddedSpec (A := A) spec) μ) :
    IsAdmissibleInitialLaw spec (worldMarginal (A := A) μ) := by
  unfold IsAdmissibleInitialLaw at hμ ⊢
  unfold worldMarginal
  rw [ProbabilityMeasure.toMeasure_map,
      Measure.map_apply measurable_snd spec.basin_measurable]
  have hsub :
      ({initialStrategicState (A := A)} ×ˢ spec.basin :
        Set (JointState (PaperIStrategicState A) X))
        ⊆ Prod.snd ⁻¹' spec.basin := by
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    exact hx
  have hle := measure_mono hsub
  have hmass :
      μ.toMeasure
        ({initialStrategicState (A := A)} ×ˢ spec.basin) = 1 := by
    simpa [embeddedSpec] using hμ
  apply le_antisymm prob_le_one
  simpa [hmass] using hle

theorem embeddedReferenceMeasure_region
    [MeasurableSingletonClass A]
    (spec : RegimeSpecification X H)
    (m : Measure X) :
    embeddedReferenceMeasure (A := A) m
      (embeddedSpec (A := A) spec).region =
      m spec.region := by
  unfold embeddedReferenceMeasure embeddedSpec
  rw [Measure.map_apply
    (initialEmbedding_measurable (X := X) (A := A))
    (MeasurableSet.univ.prod spec.region_measurable)]
  congr 1
  ext x
  simp [initialEmbedding]

/-- The lifted descriptor occupation values are literally the Paper-I
descriptor occupation values on projected world paths. -/
theorem embedded_empiricalOccupation_eq
    [MeasurableSingletonClass A]
    (spec : RegimeSpecification X H)
    (w : ℕ → JointState (PaperIStrategicState A) X)
    (T : ℕ) (hT : 0 < T) :
    RegimeSpecification.empiricalOccupation
        (embeddedSpec (A := A) spec) w T hT =
      empiricalOccupation spec
        (worldPathProjection
          (X := X) (S := PaperIStrategicState A) w)
        T hT := by
  apply ProbabilityMeasure.toMeasure_injective
  rfl

end PaperISelectedModel

end PermanssonLean
