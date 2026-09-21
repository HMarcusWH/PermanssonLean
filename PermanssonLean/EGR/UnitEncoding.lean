import PermanssonLean.EGR.Model
import PermanssonLean.StrategicWorld.InducedKernel
import Mathlib.Probability.Kernel.Deterministic

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uX uA

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA}
variable [MeasurableSpace X] [MeasurableSpace A]

/-- Canonical no-memory strategic wrapper of the selected Paper-I process.
The strategic coordinate is semantically inert; it exists only so the already
formalized strategic-world path-law machinery can represent the original
equilibrium-induced Markov chain. -/
noncomputable def unitModel
    (M : PaperISelectedModel X A) :
    StrategicWorldModel Unit X A where
  generator := {
    action := Kernel.deterministic
      (fun y : JointState Unit X => M.policy y.2)
      (M.policy_measurable.comp measurable_snd)
    update := Kernel.deterministic
      (fun _ : UpdateInput Unit X A => ())
      (by fun_prop)
    action_isMarkov := by infer_instance
    update_isMarkov := by infer_instance
  }
  world := M.world.comap
    (fun z : WorldInput Unit X A => (z.1.2, z.2))
    (by fun_prop)
  world_isMarkov := by
    letI : IsMarkovKernel M.world := M.world_isMarkov
    infer_instance

/-- The canonical unit-state embedding of a Paper-I world state. -/
def unitEmbedding : X → JointState Unit X :=
  fun x => ((), x)

theorem unitEmbedding_measurable :
    Measurable (unitEmbedding (X := X)) := by
  fun_prop

/-- World projection from the canonical unit strategic wrapper. -/
def unitWorldProjection : JointState Unit X → X :=
  Prod.snd

theorem unitWorldProjection_measurable :
    Measurable (unitWorldProjection (X := X)) :=
  measurable_snd

/-- The induced kernel of the canonical unit wrapper has exactly the selected
Paper-I equilibrium kernel as its world marginal. -/
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

end PaperISelectedModel

end PermanssonLean
