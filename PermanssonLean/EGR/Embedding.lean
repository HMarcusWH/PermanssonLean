import PermanssonLean.EGR.Model
import PermanssonLean.StrategicWorld.InducedKernel
import Mathlib.Probability.Kernel.Deterministic

open MeasureTheory ProbabilityTheory

namespace PermanssonLean

universe uX uA

/-- Paper-I action record A ∪ {⊥}; Sum.inl () is the distinguished
pre-history symbol and Sum.inr a records a realized action. -/
abbrev PaperIActionRecord (A : Type uA) := Unit ⊕ A

/-- Strategic state S_E = ℕ₀ × (A ∪ {⊥}) from the v0.1.7 embedding. -/
abbrev PaperIStrategicState (A : Type uA) := ℕ × PaperIActionRecord A

namespace PaperISelectedModel

variable {X : Type uX} {A : Type uA}
variable [MeasurableSpace X] [MeasurableSpace A]

/-- Initial strategic record (0, ⊥). -/
def initialStrategicState : PaperIStrategicState A :=
  (0, Sum.inl ())

/-- Canonical initial embedding ι₀(x)=((0,⊥),x). -/
def initialEmbedding :
    X → JointState (PaperIStrategicState A) X :=
  fun x => (initialStrategicState, x)

theorem initialEmbedding_measurable :
    Measurable (initialEmbedding (X := X) (A := A)) :=
  measurable_const.prodMk measurable_id

/-- Deterministic selected-policy action map on the enlarged state. -/
def embeddedActionMap
    (M : PaperISelectedModel X A) :
    JointState (PaperIStrategicState A) X → A :=
  fun y => M.policy y.2

theorem embeddedActionMap_measurable
    (M : PaperISelectedModel X A) :
    Measurable M.embeddedActionMap :=
  M.policy_measurable.comp measurable_snd

/-- Recording update ((t,ā),x,a,x') ↦ (t+1,a). -/
def recordingUpdateMap :
    UpdateInput (PaperIStrategicState A) X A →
      PaperIStrategicState A :=
  fun z => (z.1.1.1.1 + 1, Sum.inr z.1.2)

theorem recordingUpdateMap_measurable :
    Measurable (recordingUpdateMap (X := X) (A := A)) := by
  have ht :
      Measurable
        (fun z : UpdateInput (PaperIStrategicState A) X A =>
          z.1.1.1.1) :=
    measurable_fst.comp
      (measurable_fst.comp
        (measurable_fst.comp measurable_fst))
  have hsucc :
      Measurable
        (fun z : UpdateInput (PaperIStrategicState A) X A =>
          z.1.1.1.1 + 1) :=
    (measurable_add_const 1).comp ht
  have ha :
      Measurable
        (fun z : UpdateInput (PaperIStrategicState A) X A =>
          (Sum.inr z.1.2 : PaperIActionRecord A)) :=
    measurable_inr.comp (measurable_snd.comp measurable_fst)
  exact hsucc.prodMk ha

/-- Forget the bookkeeping coordinate before applying the original Paper-I
world kernel. -/
def embeddedWorldInputMap :
    WorldInput (PaperIStrategicState A) X A → X × A :=
  fun z => (z.1.2, z.2)

theorem embeddedWorldInputMap_measurable :
    Measurable (embeddedWorldInputMap (X := X) (A := A)) := by
  exact (measurable_snd.comp measurable_fst).prodMk measurable_snd

/-- Canonical strategic generator (α^{π*},U^{rec}). -/
noncomputable def embeddedGenerator
    (M : PaperISelectedModel X A) :
    StrategicGenerator (PaperIStrategicState A) X A where
  action := Kernel.deterministic M.embeddedActionMap M.embeddedActionMap_measurable
  update := Kernel.deterministic
    (recordingUpdateMap (X := X) (A := A))
    (recordingUpdateMap_measurable (X := X) (A := A))
  action_isMarkov := by infer_instance
  update_isMarkov := by infer_instance

/-- Original Paper-I transition law with the strategic bookkeeping coordinate
ignored: P_E(dx' | (t,ā),x,a)=P(dx'|x,a). -/
noncomputable def embeddedWorld
    (M : PaperISelectedModel X A) :
    Kernel (WorldInput (PaperIStrategicState A) X A) X :=
  M.world.comap
    (embeddedWorldInputMap (X := X) (A := A))
    (embeddedWorldInputMap_measurable (X := X) (A := A))

theorem embeddedWorld_isMarkov
    (M : PaperISelectedModel X A) :
    IsMarkovKernel M.embeddedWorld := by
  letI : IsMarkovKernel M.world := M.world_isMarkov
  unfold embeddedWorld
  infer_instance

/-- Canonical strategic-world embedding ι(M) of the selected Paper-I process. -/
noncomputable def embeddedModel
    (M : PaperISelectedModel X A) :
    StrategicWorldModel (PaperIStrategicState A) X A where
  generator := M.embeddedGenerator
  world := M.embeddedWorld
  world_isMarkov := M.embeddedWorld_isMarkov

@[simp]
theorem embeddedModel_action
    (M : PaperISelectedModel X A) :
    M.embeddedModel.generator.action =
      Kernel.deterministic M.embeddedActionMap M.embeddedActionMap_measurable :=
  rfl

@[simp]
theorem embeddedModel_update
    (M : PaperISelectedModel X A) :
    M.embeddedModel.generator.update =
      Kernel.deterministic
        (recordingUpdateMap (X := X) (A := A))
        (recordingUpdateMap_measurable (X := X) (A := A)) :=
  rfl

@[simp]
theorem embeddedModel_world
    (M : PaperISelectedModel X A) :
    M.embeddedModel.world = M.embeddedWorld :=
  rfl

end PaperISelectedModel

end PermanssonLean
