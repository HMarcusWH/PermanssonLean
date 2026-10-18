import PermanssonResearch.MultiAgent.Protocols

/-! Direct player-two protocols. Their physical kernel is literally the original
object, including in an asymmetric game. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

namespace PermanssonResearch.MultiAgent.PlayerTwoProtocols

set_option autoImplicit false
open PermanssonLean

variable {S0 S1 S2 X A1 A2 : Type*}
variable [MeasurableSpace S0] [MeasurableSpace S1] [MeasurableSpace S2]
variable [MeasurableSpace X] [MeasurableSpace A1] [MeasurableSpace A2]

/-- Replace only the second player's declared mechanism. -/
def closedLoop (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2) : TwoPlayerGenerator S0 S1 S2 X A1 A2 :=
  { G with player2 := r }

/-- Replace player two and install the declared player-one anchor. -/
def openLoop (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2) : TwoPlayerGenerator S0 S1 S2 X A1 A2 :=
  { G with player1 := a, player2 := r }

@[simp] theorem closedLoop_player1 (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2) : (closedLoop G r).player1 = G.player1 := rfl

@[simp] theorem closedLoop_common (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2) : (closedLoop G r).common = G.common := rfl

@[simp] theorem openLoop_common (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2) : (openLoop G r a).common = G.common := rfl

theorem openLoop_self (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2) :
    openLoop G r G.player1 = closedLoop G r := rfl

noncomputable def protocolFamily (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerOneMechanism S0 S1 S2 X A1 A2)) :
    InterventionFamily (G.toModel P) Protocol where
  targetOf _ := .jointStrategic
  admissible
    | .closedLoop, gen => gen = (closedLoop G r).toGenerator
    | .openLoop, gen => ∃ a ∈ anchors, gen = (openLoop G r a).toGenerator

noncomputable def closedLoopIntervention (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerOneMechanism S0 S1 S2 X A1 A2)) :
    AdmissibleStrategicIntervention (protocolFamily G P r anchors) where
  intervention := ⟨.closedLoop, (closedLoop G r).toGenerator⟩
  accepted := rfl
  strategic := InterventionTarget.isStrategic_jointStrategic

noncomputable def openLoopIntervention (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerOneMechanism S0 S1 S2 X A1 A2))
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2) (ha : a ∈ anchors) :
    AdmissibleStrategicIntervention (protocolFamily G P r anchors) where
  intervention := ⟨.openLoop, (openLoop G r a).toGenerator⟩
  accepted := ⟨a,ha,rfl⟩
  strategic := InterventionTarget.isStrategic_jointStrategic

theorem closedLoop_apply (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerOneMechanism S0 S1 S2 X A1 A2)) :
    (closedLoopIntervention G P r anchors).intervention.apply =
      (closedLoop G r).toModel P := rfl

theorem openLoop_apply (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerOneMechanism S0 S1 S2 X A1 A2))
    (a : PlayerOneMechanism S0 S1 S2 X A1 A2) (ha : a ∈ anchors) :
    (openLoopIntervention G P r anchors a ha).intervention.apply =
      (openLoop G r a).toModel P := rfl

theorem protocol_world_eq (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerOneMechanism S0 S1 S2 X A1 A2))
    (J : AdmissibleStrategicIntervention (protocolFamily G P r anchors)) :
    J.intervention.apply.world = P := J.world_eq

theorem protocol_admissible_cases (G : TwoPlayerGenerator S0 S1 S2 X A1 A2)
    (P : Kernel (WorldInput (GameState S0 S1 S2) X (A1 × A2)) X) [IsMarkovKernel P]
    (r : PlayerTwoMechanism S0 S1 S2 X A1 A2)
    (anchors : Set (PlayerOneMechanism S0 S1 S2 X A1 A2))
    (J : AdmissibleStrategicIntervention (protocolFamily G P r anchors)) :
    J.intervention.apply = (closedLoop G r).toModel P ∨
      ∃ a ∈ anchors, J.intervention.apply = (openLoop G r a).toModel P := by
  obtain ⟨⟨c,gen⟩,hacc,-⟩ := J
  cases c with
  | closedLoop =>
      left
      change ({ (G.toModel P) with generator := gen } : StrategicWorldModel _ _ _) = _
      rw [show gen = (closedLoop G r).toGenerator from hacc]
      rfl
  | openLoop =>
      right
      obtain ⟨a,ha,hgen⟩ := hacc
      refine ⟨a,ha,?_⟩
      change ({ (G.toModel P) with generator := gen } : StrategicWorldModel _ _ _) = _
      rw [show gen = (openLoop G r a).toGenerator from hgen]
      rfl

end PermanssonResearch.MultiAgent.PlayerTwoProtocols
