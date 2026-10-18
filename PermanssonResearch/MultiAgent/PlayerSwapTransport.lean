import PermanssonResearch.MultiAgent.PlayerTwoProtocols
import PermanssonResearch.MultiAgent.AutonomousKey
import PermanssonLean.Quotient.Constitution

/-! Relabel the two players, including the INPUT of the fixed physical kernel.
No invariance or symmetry assumption is made about that kernel. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.PlayerSwap

set_option autoImplicit false
open PermanssonLean

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

def strategic (s : GameState S0 S1 S2) : GameState S0 S2 S1 := (s.1,(s.2.2,s.2.1))
def state (y : JointState (GameState S0 S1 S2) X) : JointState (GameState S0 S2 S1) X :=
  (strategic y.1,y.2)
def worldInput (i : WorldInput (GameState S0 S1 S2) X (A1 × A2)) :
    WorldInput (GameState S0 S2 S1) X (A2 × A1) := (state i.1,i.2.swap)
def updateInput (i : UpdateInput (GameState S0 S1 S2) X (A1 × A2)) :
    UpdateInput (GameState S0 S2 S1) X (A2 × A1) := (worldInput i.1,i.2)

theorem measurable_strategic : Measurable (strategic (S0 := S0) (S1 := S1) (S2 := S2)) := by
  unfold strategic
  fun_prop
theorem measurable_state : Measurable (state (S0 := S0) (S1 := S1) (S2 := S2) (X := X)) := by
  unfold state
  exact (measurable_strategic.comp measurable_fst).prodMk measurable_snd
theorem measurable_worldInput :
    Measurable (worldInput (S0 := S0) (S1 := S1) (S2 := S2) (X := X)
      (A1 := A1) (A2 := A2)) := by
  unfold worldInput
  exact (measurable_state.comp measurable_fst).prodMk (measurable_swap.comp measurable_snd)
theorem measurable_updateInput :
    Measurable (updateInput (S0 := S0) (S1 := S1) (S2 := S2) (X := X)
      (A1 := A1) (A2 := A2)) := by
  unfold updateInput
  exact (measurable_worldInput.comp measurable_fst).prodMk measurable_snd

@[simp] theorem strategic_twice (s : GameState S0 S1 S2) : strategic (strategic s) = s := rfl
@[simp] theorem state_twice (y : JointState (GameState S0 S1 S2) X) : state (state y) = y := rfl
@[simp] theorem worldInput_twice (i : WorldInput (GameState S0 S1 S2) X (A1 × A2)) :
    worldInput (worldInput i) = i := rfl
@[simp] theorem updateInput_twice (i : UpdateInput (GameState S0 S1 S2) X (A1 × A2)) :
    updateInput (updateInput i) = i := rfl

noncomputable def first (a : PlayerTwoMechanism S0 S1 S2 X A1 A2) :
    PlayerOneMechanism S0 S2 S1 X A2 A1 where
  action := a.action.comap state measurable_state
  update := a.update.comap updateInput measurable_updateInput
  action_isMarkov := by letI := a.action_isMarkov; infer_instance
  update_isMarkov := by letI := a.update_isMarkov; infer_instance

noncomputable def second (a : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    PlayerTwoMechanism S0 S2 S1 X A2 A1 where
  action := a.action.comap state measurable_state
  update := a.update.comap updateInput measurable_updateInput
  action_isMarkov := by letI := a.action_isMarkov; infer_instance
  update_isMarkov := by letI := a.update_isMarkov; infer_instance

noncomputable def generator (G : TwoPlayerGenerator S0 S1 S2 X A1 A2) :
    TwoPlayerGenerator S0 S2 S1 X A2 A1 where
  player1 := first G.player2
  player2 := second G.player1
  common := G.common.comap updateInput measurable_updateInput
  common_isMarkov := by letI := G.common_isMarkov; infer_instance

/-- Pull back INPUTS only; the physical outcome space is unchanged. -/
noncomputable def physical
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) :
    Kernel (WorldInput (GameState S0 S2 S1) X (A2 × A1)) X :=
  P.comap worldInput measurable_worldInput

instance physical_isMarkov
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P] :
    IsMarkovKernel (physical P) := by unfold physical; infer_instance

noncomputable def compression :
    TypeRespectingStateCompression (GameState S0 S1 S2) X (GameState S0 S2 S1) X where
  strategic := strategic
  world := id
  strategic_measurable := measurable_strategic
  world_measurable := measurable_id
  strategic_surjective := fun s => ⟨strategic s,rfl⟩
  world_surjective := Function.surjective_id

@[simp] theorem compression_state (y : JointState (GameState S0 S1 S2) X) :
    compression.stateMap y = state y := rfl

theorem generator_closedLoop (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2) :
    generator (PlayerTwoProtocols.closedLoop G r) = (generator G).closedLoop (first r) := rfl

theorem generator_openLoop (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2) :
    generator (PlayerTwoProtocols.openLoop G r a) =
      (generator G).openLoop (first r) (second a) := rfl

section Finite
variable [Fintype S0] [Fintype S1] [Fintype S2] [Fintype X] [Fintype A1] [Fintype A2]
variable [MeasurableSingletonClass S0] [MeasurableSingletonClass S1]
variable [MeasurableSingletonClass S2] [MeasurableSingletonClass X]
variable [MeasurableSingletonClass A1] [MeasurableSingletonClass A2]

theorem actual_atom (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (y z : JointState (GameState S0 S1 S2) X) :
    ((generator G).toModel (physical P)).inducedKernel (state y) {state z} =
      (G.toModel P).inducedKernel y {z} := by
  classical
  rw [Autonomous.product_transition_atom,Autonomous.product_transition_atom,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b1 _
  apply Finset.sum_congr rfl
  intro b2 _
  simp only [generator,first,second,physical,Kernel.comap_apply,
    updateInput,worldInput,state,strategic,Prod.swap_prod_mk]
  ring

theorem actual_intertwines (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P] :
    KernelIntertwines compression (G.toModel P).inducedKernel
      ((generator G).toModel (physical P)).inducedKernel := by
  classical
  apply Kernel.ext
  intro y
  rw [Kernel.map_apply _ compression.stateMap_measurable,Kernel.comap_apply]
  apply Measure.ext_of_singleton
  intro z
  rw [Measure.map_apply compression.stateMap_measurable (measurableSet_singleton z)]
  have hset : compression.stateMap ⁻¹' ({z} : Set (JointState (GameState S0 S2 S1) X)) =
      {state z} := by
    ext w
    simp only [compression_state,Set.mem_preimage,Set.mem_singleton_iff]
    constructor
    · intro h
      have := congrArg state h
      simpa using this
    · intro h
      subst w
      exact state_twice z
  rw [hset]
  simpa using (actual_atom G P y (state z)).symm

theorem actual_pathLaw (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (μ : Measure (JointState (GameState S0 S1 S2) X)) [IsProbabilityMeasure μ] :
    ((G.toModel P).pathLaw μ).map compression.pathMap =
      ((generator G).toModel (physical P)).pathLaw (μ.map state) := by
  exact StrategicWorldModel.pathLaw_map_eq_of_kernelIntertwines compression
    _ _ (actual_intertwines G P) μ

theorem property_value {Z : Type*} (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (ψ : RegimePropertyMap (JointState (GameState S0 S1 S2) X) Z)
    (ψbar : RegimePropertyMap (JointState (GameState S0 S2 S1) X) Z)
    (hψ : PropertyFactorsThroughCompression compression ψ ψbar)
    (y : JointState (GameState S0 S1 S2) X) :
    RegimeSpecification.baselinePropertyValue ψ (G.toModel P) y =
      RegimeSpecification.baselinePropertyValue ψbar
        ((generator G).toModel (physical P)) (state y) := by
  exact RegimeSpecification.baselinePropertyValue_eq_under_quotient compression
    _ _ (actual_intertwines G P) ψ ψbar hψ y

end Finite
end PermanssonResearch.MultiAgent.PlayerSwap
