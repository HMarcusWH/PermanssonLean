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
  rw [StrategicWorldModel.inducedKernel_apply
    M.unitModel ((), x) (hD.preimage measurable_snd)]
  simp [unitModel, equilibriumKernel,
    Kernel.comap_apply', Kernel.deterministic_apply,
    Kernel.lintegral_deterministic']

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
      M.pathLaw
        ((μ0.toMeasure.map measurable_snd).map
          (unitWorldProjection (X := X))) := by
  have hpush :=
    StrategicWorldModel.pathLaw_map_eq_of_kernelIntertwines
      (recordingCompression (X := X) (A := A))
      M.embeddedModel M.unitModel
      M.embedded_unit_kernelIntertwines
      μ0.toMeasure
  unfold pathLaw
  rw [← hpush]
  rw [Measure.map_map
    (worldPathProjection_measurable (X := X) (S := Unit))
    (recordingCompression (X := X) (A := A)).pathMap_measurable]
  rw [Measure.map_map
    (recordingCompression (X := X) (A := A)).stateMap_measurable
    measurable_snd]
  rw [Measure.map_map
    (unitEmbedding_measurable (X := X))
    measurable_snd]
  congr 1 <;> funext z <;> rfl

end PaperISelectedModel

end PermanssonLean
