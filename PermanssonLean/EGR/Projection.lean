import PermanssonLean.EGR.Embedding
import PermanssonLean.Quotient.PathLaw

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uX uA

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA}
variable [MeasurableSpace X] [MeasurableSpace A]

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

end PaperISelectedModel

end PermanssonLean
