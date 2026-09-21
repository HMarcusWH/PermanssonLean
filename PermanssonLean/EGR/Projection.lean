import PermanssonLean.EGR.Embedding
import PermanssonLean.Quotient.PathLaw

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uX uA

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA}
variable [MeasurableSpace X] [MeasurableSpace A]


/-- The Unit wrapper's one-step law on a world-cylinder is exactly the
Paper-I equilibrium-induced kernel. -/
theorem unitModel_induced_apply
    (M : PaperISelectedModel X A)
    (x : X)
    {D : Set X} (hD : MeasurableSet D) :
    M.unitModel.inducedKernel ((), x)
      (unitWorldProjection ⁻¹' D) =
      M.equilibriumKernel x D := by
  change M.unitModel.inducedKernel ((), x) (Prod.snd ⁻¹' D) =
    M.equilibriumKernel x D
  rw [StrategicWorldModel.inducedKernel_apply
    M.unitModel ((), x) (hD.preimage measurable_snd)]
  simp [unitModel, equilibriumKernel,
    Kernel.comap_apply', Kernel.deterministic_apply,
    Kernel.lintegral_deterministic']
  have hinner (a : A) :
      (∫⁻ x' : X,
        {s' : Unit | x' ∈ D}.indicator 1 () ∂M.world (x, a)) =
        M.world (x, a) D := by
    calc
      (∫⁻ x' : X,
        {s' : Unit | x' ∈ D}.indicator 1 () ∂M.world (x, a)) =
          ∫⁻ x' : X, D.indicator 1 x' ∂M.world (x, a) := by
            apply lintegral_congr
            intro x'
            simp [Set.indicator_apply]
      _ = M.world (x, a) D := lintegral_indicator_one hD
  simp_rw [hinner]
  rw [lintegral_dirac' _]
  exact (Kernel.measurable_coe M.world hD).comp
    (measurable_const.prodMk measurable_id)

/-- Type-respecting projection that forgets the Paper-II recording state while
leaving the Paper-I world coordinate unchanged. -/
def recordingCompression :
    TypeRespectingStateCompression
      (PaperIStrategicState A) X Unit X where
  strategic := fun _ => ()
  world := id
  strategic_measurable := by fun_prop
  world_measurable := measurable_id
  strategic_surjective := by
    intro u
    exact ⟨initialStrategicState, Subsingleton.elim _ _⟩
  world_surjective := Function.surjective_id

@[simp]
theorem recordingCompression_stateMap
    (y : JointState (PaperIStrategicState A) X) :
    (recordingCompression (X := X) (A := A)).stateMap y =
      ((), y.2) :=
  rfl

/-- Equation (18) in kernel-intertwining form: forgetting the clock/action
record from the embedded one-step law yields the canonical unit-state
encoding of the Paper-I equilibrium process. -/
theorem embedded_unit_kernelIntertwines
    (M : PaperISelectedModel X A) :
    KernelIntertwines
      (recordingCompression (X := X) (A := A))
      M.embeddedModel.inducedKernel
      M.unitModel.inducedKernel := by
  unfold KernelIntertwines
  ext y C hC
  rw [Kernel.map_apply' _
    (recordingCompression (X := X) (A := A)).stateMap_measurable y hC,
    Kernel.comap_apply']
  rw [StrategicWorldModel.inducedKernel_apply
    M.embeddedModel y
    (hC.preimage
      (recordingCompression (X := X) (A := A)).stateMap_measurable)]
  rw [StrategicWorldModel.inducedKernel_apply
    M.unitModel
    ((recordingCompression (X := X) (A := A)).stateMap y) hC]
  simp [embeddedModel, embeddedGenerator, embeddedWorld,
    unitModel, recordingCompression, TypeRespectingStateCompression.stateMap,
    embeddedActionMap, embeddedWorldInputMap, recordingUpdateMap,
    equilibriumKernel, Kernel.comap_apply',
    Kernel.deterministic_apply, Kernel.lintegral_deterministic']
  congr with a

/-- Baseline canonical path laws commute with the recording projection. -/
theorem embedded_pathProbability_push_unit
    (M : PaperISelectedModel X A)
    (μ0 : ProbabilityMeasure
      (JointState (PaperIStrategicState A) X)) :
    (recordingCompression (X := X) (A := A)).pushPath
        (RegimeSpecification.pathProbability M.embeddedModel μ0) =
      RegimeSpecification.pathProbability M.unitModel
        ((recordingCompression (X := X) (A := A)).pushInitial μ0) := by
  exact RegimeSpecification.pathProbability_push_eq_of_kernelIntertwines
    (recordingCompression (X := X) (A := A))
    M.embeddedModel M.unitModel
    M.embedded_unit_kernelIntertwines μ0


/-- For an arbitrary enlarged initial law, the world-path marginal of the
recording embedding is exactly the Paper-I path law started from the enlarged
law's world marginal. -/
theorem embedded_worldPathLaw_eq_paperI
    (M : PaperISelectedModel X A)
    (μ0 : ProbabilityMeasure
      (JointState (PaperIStrategicState A) X)) :
    (M.embeddedModel.pathLaw μ0.toMeasure).map
        (worldPathProjection
          (X := X) (S := PaperIStrategicState A)) =
      M.pathLaw (μ0.map Prod.snd).toMeasure := by
  have hpush :=
    StrategicWorldModel.pathLaw_map_eq_of_kernelIntertwines
      (recordingCompression (X := X) (A := A))
      M.embeddedModel M.unitModel
      M.embedded_unit_kernelIntertwines
      μ0.toMeasure
  have hinit :
      μ0.toMeasure.map
          (recordingCompression (X := X) (A := A)).stateMap =
        (μ0.map Prod.snd).toMeasure.map
          (unitEmbedding (X := X)) := by
    rw [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map
      (unitEmbedding_measurable (X := X))
      measurable_snd]
    apply Measure.map_congr
    filter_upwards [] with y
    rfl
  have pathLaw_congr_initial
      {μ ν : Measure (JointState Unit X)}
      [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
      (hμν : μ = ν) :
      M.unitModel.pathLaw μ = M.unitModel.pathLaw ν := by
    subst ν
    rfl
  have hpathInit :
      M.unitModel.pathLaw
          (μ0.toMeasure.map
            (recordingCompression (X := X) (A := A)).stateMap) =
        M.unitModel.pathLaw
          ((μ0.map Prod.snd).toMeasure.map
            (unitEmbedding (X := X))) :=
    pathLaw_congr_initial hinit
  unfold pathLaw
  calc
    (M.embeddedModel.pathLaw μ0.toMeasure).map
        (worldPathProjection
          (X := X) (S := PaperIStrategicState A)) =
      ((M.embeddedModel.pathLaw μ0.toMeasure).map
        (recordingCompression (X := X) (A := A)).pathMap).map
          (worldPathProjection (X := X) (S := Unit)) := by
        rw [Measure.map_map
          (worldPathProjection_measurable (X := X) (S := Unit))
          (recordingCompression (X := X) (A := A)).pathMap_measurable]
        apply Measure.map_congr
        filter_upwards [] with w
        rfl
    _ = (M.unitModel.pathLaw
          (μ0.toMeasure.map
            (recordingCompression (X := X) (A := A)).stateMap)).map
          (worldPathProjection (X := X) (S := Unit)) := by
        rw [hpush]
    _ = (M.unitModel.pathLaw
          ((μ0.map Prod.snd).toMeasure.map
            (unitEmbedding (X := X)))).map
          (worldPathProjection (X := X) (S := Unit)) := by
        rw [hpathInit]

end PaperISelectedModel

end PermanssonLean
